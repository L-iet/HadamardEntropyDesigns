/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch27
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3584 : Finset ℕ := ([40,48,132,222,1628,1642,1650,1714,1734,1768,1776,2618,2638,2646,2680,2702,2710,2764,2772,2786,3130,3150,3158,3192,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3584 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3584 2702 4
  · have he : independentCachedBranchMembers3584.erase 2702=independentCachedBranchMembers3580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3580
  · have he : independentCachedBranchMembers3584.filter (independentCachedEdge 2702)=independentCachedBranchMembers3583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3583
def independentCachedBranchMembers3585 : Finset ℕ := ([12,40,48,132,222,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1740,1748,1762,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3585 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3585 1762 5
  · have he : independentCachedBranchMembers3585.erase 1762=independentCachedBranchMembers3567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3567
  · have he : independentCachedBranchMembers3585.filter (independentCachedEdge 1762)=independentCachedBranchMembers3584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3584
def independentCachedBranchMembers3586 : Finset ℕ := ([48,132,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2764,2800,3158,3178,3192,3214,3228,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3586 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3586 5 (fun x => (if x<2680 then (if x<1720 then (if x<1628 then (if x<132 then 0 else 0) else (if x<1650 then 1 else (if x<1686 then 0 else 1))) else (if x<1768 then (if x<1734 then 1 else (if x<1748 then 0 else 2)) else (if x<2618 then 2 else (if x<2646 then 0 else 1)))) else (if x<3178 then (if x<2764 then (if x<2716 then 1 else 1) else (if x<2800 then 2 else (if x<3158 then 2 else 3))) else (if x<3228 then (if x<3192 then 3 else (if x<3214 then 0 else 3)) else (if x<3250 then 4 else (if x<3276 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3587 : Finset ℕ := ([1628,1686,1768,2618,2646,2716,2800,3178,3192,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3587 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3587 4 (fun x => (if x<2716 then (if x<1768 then (if x<1686 then 0 else 0) else (if x<2618 then 1 else (if x<2646 then 2 else 0))) else (if x<3192 then (if x<2800 then 0 else (if x<3178 then 1 else 2)) else (if x<3250 then 1 else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3588 : Finset ℕ := ([48,132,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2764,2800,3130,3158,3178,3192,3214,3228,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3588 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3588 3130 4
  · have he : independentCachedBranchMembers3588.erase 3130=independentCachedBranchMembers3586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3586
  · have he : independentCachedBranchMembers3588.filter (independentCachedEdge 3130)=independentCachedBranchMembers3587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3587
def independentCachedBranchMembers3589 : Finset ℕ := ([132,1628,1686,1734,2618,2646,2716,2764,2800,3192,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3589 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3589 4 (fun x => (if x<2716 then (if x<1734 then (if x<1628 then 0 else (if x<1686 then 1 else 0)) else (if x<2618 then 1 else (if x<2646 then 2 else 1))) else (if x<3192 then (if x<2764 then 0 else (if x<2800 then 1 else 2)) else (if x<3214 then 2 else (if x<3250 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3590 : Finset ℕ := ([48,132,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2764,2800,3130,3158,3178,3192,3214,3228,3250,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3590 3312 4
  · have he : independentCachedBranchMembers3590.erase 3312=independentCachedBranchMembers3588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3588
  · have he : independentCachedBranchMembers3590.filter (independentCachedEdge 3312)=independentCachedBranchMembers3589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3589
def independentCachedBranchMembers3591 : Finset ℕ := ([48,132,1686,1720,1748,2716,2800,3130,3158,3192,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3591 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3591 4 (fun x => (if x<2800 then (if x<1720 then (if x<132 then 0 else (if x<1686 then 0 else 1)) else (if x<1748 then 1 else (if x<2716 then 2 else 1))) else (if x<3192 then (if x<3130 then 2 else (if x<3158 then 0 else 3)) else (if x<3214 then 3 else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3592 : Finset ℕ := ([48,132,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2764,2786,2800,3130,3158,3178,3192,3214,3228,3250,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3592 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3592 2786 4
  · have he : independentCachedBranchMembers3592.erase 2786=independentCachedBranchMembers3590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3590
  · have he : independentCachedBranchMembers3592.filter (independentCachedEdge 2786)=independentCachedBranchMembers3591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3591
def independentCachedBranchMembers3593 : Finset ℕ := ([132,1628,1686,1734,1748,2646,2716,2764,3158,3214,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3593 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3593 4 (fun x => (if x<2716 then (if x<1734 then (if x<1628 then 0 else (if x<1686 then 1 else 0)) else (if x<1748 then 1 else (if x<2646 then 2 else 1))) else (if x<3214 then (if x<2764 then 0 else (if x<3158 then 1 else 2)) else (if x<3228 then 0 else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3594 : Finset ℕ := ([48,132,250,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2764,2786,2800,3130,3158,3178,3192,3214,3228,3250,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3594 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3594 250 4
  · have he : independentCachedBranchMembers3594.erase 250=independentCachedBranchMembers3592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3592
  · have he : independentCachedBranchMembers3594.filter (independentCachedEdge 250)=independentCachedBranchMembers3593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3593
def independentCachedBranchMembers3595 : Finset ℕ := ([132,1686,1720,1748,2618,2646,2680,2764,2786,3178,3228,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3595 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3595 4 (fun x => (if x<2680 then (if x<1748 then (if x<1686 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2646 then 1 else 1))) else (if x<3178 then (if x<2764 then 0 else (if x<2786 then 2 else 2)) else (if x<3250 then (if x<3228 then 0 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3596 : Finset ℕ := ([1686,1748,2646,2786,3178,3228] : List ℕ).toFinset
theorem independentCachedBranchBound3596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3596 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3596 3 (fun x => (if x<2786 then (if x<1748 then 0 else (if x<2646 then 1 else 0)) else (if x<3178 then 2 else (if x<3228 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3597 : Finset ℕ := ([48,132,1686,1720,1748,2618,2646,2680,2764,2786,3178,3228,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3597 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3597 48 3
  · have he : independentCachedBranchMembers3597.erase 48=independentCachedBranchMembers3595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3595
  · have he : independentCachedBranchMembers3597.filter (independentCachedEdge 48)=independentCachedBranchMembers3596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3596
def independentCachedBranchMembers3598 : Finset ℕ := ([48,132,250,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2764,2786,2800,3130,3158,3178,3192,3214,3228,3250,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3598 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3598 3298 4
  · have he : independentCachedBranchMembers3598.erase 3298=independentCachedBranchMembers3594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3594
  · have he : independentCachedBranchMembers3598.filter (independentCachedEdge 3298)=independentCachedBranchMembers3597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3597
def independentCachedBranchMembers3599 : Finset ℕ := ([132,1734,1748,1768,2618,2764,2800,3158,3178,3192,3214,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3599 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3599 4 (fun x => (if x<2800 then (if x<1768 then (if x<1734 then 0 else (if x<1748 then 0 else 1)) else (if x<2618 then 1 else (if x<2764 then 0 else 1))) else (if x<3192 then (if x<3158 then 1 else (if x<3178 then 2 else 2)) else (if x<3228 then (if x<3214 then 0 else 2) else (if x<3250 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3600 : Finset ℕ := ([132,1748,2800,3158,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound3600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3600 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3600 3 (fun x => (if x<3158 then (if x<1748 then 0 else (if x<2800 then 0 else 1)) else (if x<3192 then 2 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3601 : Finset ℕ := ([132,1734,1748,1768,2618,2764,2786,2800,3158,3178,3192,3214,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3601 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3601 2786 3
  · have he : independentCachedBranchMembers3601.erase 2786=independentCachedBranchMembers3599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3599
  · have he : independentCachedBranchMembers3601.filter (independentCachedEdge 2786)=independentCachedBranchMembers3600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3600
def independentCachedBranchMembers3602 : Finset ℕ := ([48,132,250,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2738,2764,2786,2800,3130,3158,3178,3192,3214,3228,3250,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3602 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3602 2738 4
  · have he : independentCachedBranchMembers3602.erase 2738=independentCachedBranchMembers3598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3598
  · have he : independentCachedBranchMembers3602.filter (independentCachedEdge 2738)=independentCachedBranchMembers3601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3601
def independentCachedBranchMembers3603 : Finset ℕ := ([132,250,1686,1720,1734,1748,1768,2618,2646,2680,3130,3158,3178,3192] : List ℕ).toFinset
theorem independentCachedBranchBound3603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3603 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3603 4 (fun x => (if x<2618 then (if x<1720 then (if x<250 then 0 else (if x<1686 then 1 else 0)) else (if x<1748 then (if x<1734 then 1 else 2) else (if x<1768 then 3 else 2))) else (if x<3130 then (if x<2646 then 1 else (if x<2680 then 2 else 0)) else (if x<3178 then (if x<3158 then 3 else 3) else (if x<3192 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3604 : Finset ℕ := ([12,48,132,250,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2716,2738,2764,2786,2800,3130,3158,3178,3192,3214,3228,3250,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3604 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3604 12 4
  · have he : independentCachedBranchMembers3604.erase 12=independentCachedBranchMembers3602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3602
  · have he : independentCachedBranchMembers3604.filter (independentCachedEdge 12)=independentCachedBranchMembers3603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3603
def independentCachedBranchMembers3605 : Finset ℕ := ([1628,1720,1748,1768,2680,2716,2764,2800,3130,3158,3178,3214,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3605 4 (fun x => (if x<2800 then (if x<1768 then (if x<1720 then 0 else (if x<1748 then 0 else 1)) else (if x<2716 then (if x<2680 then 1 else 0) else (if x<2764 then 0 else 1))) else (if x<3178 then (if x<3130 then 1 else (if x<3158 then 2 else 2)) else (if x<3250 then (if x<3214 then 3 else 2) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3606 : Finset ℕ := ([1628,1748,2716,2764,3158,3214] : List ℕ).toFinset
theorem independentCachedBranchBound3606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3606 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3606 3 (fun x => (if x<2764 then (if x<1748 then 0 else (if x<2716 then 1 else 0)) else (if x<3158 then 1 else (if x<3214 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3607 : Finset ℕ := ([250,1628,1720,1748,1768,2680,2716,2764,2800,3130,3158,3178,3214,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3607 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3607 250 3
  · have he : independentCachedBranchMembers3607.erase 250=independentCachedBranchMembers3605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3605
  · have he : independentCachedBranchMembers3607.filter (independentCachedEdge 250)=independentCachedBranchMembers3606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3606
def independentCachedBranchMembers3608 : Finset ℕ := ([12,48,132,250,1628,1650,1686,1720,1734,1748,1768,2618,2646,2680,2702,2716,2738,2764,2786,2800,3130,3158,3178,3192,3214,3228,3250,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3608 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3608 2702 4
  · have he : independentCachedBranchMembers3608.erase 2702=independentCachedBranchMembers3604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3604
  · have he : independentCachedBranchMembers3608.filter (independentCachedEdge 2702)=independentCachedBranchMembers3607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3607
def independentCachedBranchMembers3609 : Finset ℕ := ([12,40,48,132,222,250,1594,1622,1628,1642,1650,1678,1686,1714,1720,1734,1740,1748,1762,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3609 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3609 1622 5
  · have he : independentCachedBranchMembers3609.erase 1622=independentCachedBranchMembers3585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3585
  · have he : independentCachedBranchMembers3609.filter (independentCachedEdge 1622)=independentCachedBranchMembers3608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3608
def independentCachedBranchMembers3610 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1686,1720,1734,1768,1776,2618,2674,2710,2758,2792,2800,3102,3158,3192,3250,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3610 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3610 5 (fun x => (if x<2618 then (if x<1642 then (if x<250 then (if x<48 then 0 else (if x<132 then 1 else 0)) else (if x<1594 then 1 else (if x<1628 then 0 else 2))) else (if x<1720 then (if x<1650 then 2 else (if x<1686 then 1 else 0)) else (if x<1768 then (if x<1734 then 1 else 2) else (if x<1776 then 3 else 2)))) else (if x<3102 then (if x<2758 then (if x<2674 then 1 else (if x<2710 then 4 else 3)) else (if x<2792 then 0 else (if x<2800 then 4 else 1))) else (if x<3250 then (if x<3158 then 3 else (if x<3192 then 4 else 0)) else (if x<3284 then (if x<3276 then 1 else 4) else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3611 : Finset ℕ := ([40,250,1650,1686,1734,1776,2618,2792,3158,3250,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3611 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3611 4 (fun x => (if x<2618 then (if x<1686 then (if x<250 then 0 else (if x<1650 then 0 else 1)) else (if x<1734 then 1 else (if x<1776 then 2 else 2))) else (if x<3250 then (if x<2792 then 0 else (if x<3158 then 0 else 1)) else (if x<3284 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3612 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1720,1734,1768,1776,2618,2674,2710,2758,2792,2800,3102,3158,3192,3250,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3612 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3612 1678 4
  · have he : independentCachedBranchMembers3612.erase 1678=independentCachedBranchMembers3610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3610
  · have he : independentCachedBranchMembers3612.filter (independentCachedEdge 1678)=independentCachedBranchMembers3611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3611
def independentCachedBranchMembers3613 : Finset ℕ := ([48,132,1650,1686,1734,1776,2674,2710,2758,2800,3158,3250,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3613 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3613 4 (fun x => (if x<2710 then (if x<1686 then (if x<132 then 0 else (if x<1650 then 0 else 0)) else (if x<1776 then (if x<1734 then 1 else 0) else (if x<2674 then 1 else 2))) else (if x<3158 then (if x<2758 then 2 else (if x<2800 then 3 else 3)) else (if x<3284 then (if x<3250 then 2 else 1) else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3614 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1720,1734,1768,1776,2618,2674,2710,2758,2792,2800,3102,3158,3192,3242,3250,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3614 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3614 3242 4
  · have he : independentCachedBranchMembers3614.erase 3242=independentCachedBranchMembers3612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3612
  · have he : independentCachedBranchMembers3614.filter (independentCachedEdge 3242)=independentCachedBranchMembers3613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3613
def independentCachedBranchMembers3615 : Finset ℕ := ([40,48,250,1594,1734,1768,1776,2618,2758,2792,2800,3102,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3615 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3615 4 (fun x => (if x<2618 then (if x<1594 then (if x<48 then 0 else (if x<250 then 1 else 0)) else (if x<1768 then (if x<1734 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3102 then (if x<2792 then (if x<2758 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3284 then (if x<3276 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3616 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1720,1734,1768,1776,2618,2674,2710,2758,2792,2800,3102,3158,3192,3228,3242,3250,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3616 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3616 3228 4
  · have he : independentCachedBranchMembers3616.erase 3228=independentCachedBranchMembers3614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3614
  · have he : independentCachedBranchMembers3616.filter (independentCachedEdge 3228)=independentCachedBranchMembers3615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3615
def independentCachedBranchMembers3617 : Finset ℕ := ([40,132,250,1594,1650,1686,1768,2618,2674,2710,2792,3102,3158,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3617 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3617 4 (fun x => (if x<2618 then (if x<1594 then (if x<132 then 0 else (if x<250 then 0 else 1)) else (if x<1686 then (if x<1650 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<3102 then (if x<2710 then (if x<2674 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3250 then (if x<3158 then 2 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3618 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1720,1734,1768,1776,2618,2674,2710,2758,2792,2800,3102,3150,3158,3192,3228,3242,3250,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3618 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3618 3150 4
  · have he : independentCachedBranchMembers3618.erase 3150=independentCachedBranchMembers3616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3616
  · have he : independentCachedBranchMembers3618.filter (independentCachedEdge 3150)=independentCachedBranchMembers3617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3617
def independentCachedBranchMembers3619 : Finset ℕ := ([40,250,1594,1628,1642,1678,1720,1768,2674,2710,2758,2800,3158,3250,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3619 4 (fun x => (if x<2674 then (if x<1642 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1720 then (if x<1678 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3158 then (if x<2758 then (if x<2710 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3284 then (if x<3250 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3620 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1720,1734,1768,1776,2618,2674,2702,2710,2758,2792,2800,3102,3150,3158,3192,3228,3242,3250,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3620 2702 4
  · have he : independentCachedBranchMembers3620.erase 2702=independentCachedBranchMembers3618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3618
  · have he : independentCachedBranchMembers3620.filter (independentCachedEdge 2702)=independentCachedBranchMembers3619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3619
def independentCachedBranchMembers3621 : Finset ℕ := ([12,40,48,132,222,250,1594,1622,1628,1642,1650,1678,1686,1714,1720,1734,1740,1748,1762,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3621 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3621 3164 5
  · have he : independentCachedBranchMembers3621.erase 3164=independentCachedBranchMembers3609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3609
  · have he : independentCachedBranchMembers3621.filter (independentCachedEdge 3164)=independentCachedBranchMembers3620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3620
def independentCachedBranchMembers3622 : Finset ℕ := ([48,250,1628,1642,1650,1678,1686,1720,1740,1748,1762,2618,2638,2680,2716,2730,2738,2758,2792,3130,3158,3192,3228,3242,3250,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3622 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3622 5 (fun x => (if x<2680 then (if x<1686 then (if x<1642 then (if x<250 then 0 else (if x<1628 then 0 else 1)) else (if x<1650 then 1 else (if x<1678 then 0 else 1))) else (if x<1748 then (if x<1720 then 2 else (if x<1740 then 0 else 2)) else (if x<2618 then (if x<1762 then 3 else 2) else (if x<2638 then 0 else 1)))) else (if x<3158 then (if x<2738 then (if x<2716 then 1 else (if x<2730 then 1 else 1)) else (if x<2792 then (if x<2758 then 2 else 2) else (if x<3130 then 2 else 3))) else (if x<3242 then (if x<3192 then 3 else (if x<3228 then 0 else 3)) else (if x<3270 then (if x<3250 then 4 else 0) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3623 : Finset ℕ := ([48,1628,1650,1678,1740,1762,2638,2716,2738,3228,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3623 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3623 4 (fun x => (if x<2638 then (if x<1678 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<1740 then 1 else (if x<1762 then 2 else 2))) else (if x<3228 then (if x<2716 then 1 else (if x<2738 then 1 else 0)) else (if x<3250 then 2 else (if x<3312 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3624 : Finset ℕ := ([40,48,250,1628,1642,1650,1678,1686,1720,1740,1748,1762,2618,2638,2680,2716,2730,2738,2758,2792,3130,3158,3192,3228,3242,3250,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3624 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3624 40 4
  · have he : independentCachedBranchMembers3624.erase 40=independentCachedBranchMembers3622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3622
  · have he : independentCachedBranchMembers3624.filter (independentCachedEdge 40)=independentCachedBranchMembers3623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3623
def independentCachedBranchMembers3625 : Finset ℕ := ([1628,1642,1686,1740,2638,2680,2738,2792,3130,3158,3228,3242,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3625 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3625 4 (fun x => (if x<2792 then (if x<1740 then (if x<1642 then 0 else (if x<1686 then 0 else 1)) else (if x<2680 then (if x<2638 then 1 else 0) else (if x<2738 then 0 else 1))) else (if x<3228 then (if x<3130 then 1 else (if x<3158 then 2 else 2)) else (if x<3270 then (if x<3242 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3626 : Finset ℕ := ([1628,1740,2638,2738,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3626 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3626 3 (fun x => (if x<2738 then (if x<1740 then 0 else (if x<2638 then 1 else 0)) else (if x<3228 then 1 else (if x<3312 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3627 : Finset ℕ := ([40,1628,1642,1686,1740,2638,2680,2738,2792,3130,3158,3228,3242,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3627 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3627 40 3
  · have he : independentCachedBranchMembers3627.erase 40=independentCachedBranchMembers3625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3625
  · have he : independentCachedBranchMembers3627.filter (independentCachedEdge 40)=independentCachedBranchMembers3626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3626
def independentCachedBranchMembers3628 : Finset ℕ := ([40,48,250,1628,1642,1650,1678,1686,1720,1740,1748,1762,2618,2638,2680,2716,2730,2738,2758,2792,2800,3130,3158,3192,3228,3242,3250,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3628 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3628 2800 4
  · have he : independentCachedBranchMembers3628.erase 2800=independentCachedBranchMembers3624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3624
  · have he : independentCachedBranchMembers3628.filter (independentCachedEdge 2800)=independentCachedBranchMembers3627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3627
def independentCachedBranchMembers3629 : Finset ℕ := ([250,1650,1686,1748,1762,2618,2638,2680,2716,2730,2792,3158,3250,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3629 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3629 4 (fun x => (if x<2680 then (if x<1748 then (if x<1650 then 0 else (if x<1686 then 0 else 1)) else (if x<2618 then (if x<1762 then 2 else 1) else (if x<2638 then 0 else 3))) else (if x<3158 then (if x<2730 then (if x<2716 then 3 else 1) else (if x<2792 then 2 else 1)) else (if x<3270 then (if x<3250 then 2 else 0) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3630 : Finset ℕ := ([1650,1762,2638,2716,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3630 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3630 3 (fun x => (if x<2716 then (if x<1762 then 0 else (if x<2638 then 1 else 2)) else (if x<3250 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3631 : Finset ℕ := ([40,250,1650,1686,1748,1762,2618,2638,2680,2716,2730,2792,3158,3250,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3631 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3631 40 3
  · have he : independentCachedBranchMembers3631.erase 40=independentCachedBranchMembers3629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3629
  · have he : independentCachedBranchMembers3631.filter (independentCachedEdge 40)=independentCachedBranchMembers3630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3630
def independentCachedBranchMembers3632 : Finset ℕ := ([40,48,250,1628,1642,1650,1678,1686,1720,1740,1748,1762,2618,2638,2680,2716,2730,2738,2758,2792,2800,3130,3150,3158,3192,3228,3242,3250,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3632 3150 4
  · have he : independentCachedBranchMembers3632.erase 3150=independentCachedBranchMembers3628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3628
  · have he : independentCachedBranchMembers3632.filter (independentCachedEdge 3150)=independentCachedBranchMembers3631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3631
def independentCachedBranchMembers3633 : Finset ℕ := ([48,250,1642,1678,1740,1762,2638,2730,2758,2792,3130,3158,3192,3228,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3633 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3633 4 (fun x => (if x<2758 then (if x<1740 then (if x<1642 then (if x<250 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1762 then 2 else 2) else (if x<2730 then 1 else 1))) else (if x<3192 then (if x<3130 then (if x<2792 then 2 else 2) else (if x<3158 then 0 else 3)) else (if x<3250 then (if x<3228 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3634 : Finset ℕ := ([40,48,250,1628,1642,1650,1678,1686,1720,1740,1748,1762,2618,2638,2646,2680,2716,2730,2738,2758,2792,2800,3130,3150,3158,3192,3228,3242,3250,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3634 2646 4
  · have he : independentCachedBranchMembers3634.erase 2646=independentCachedBranchMembers3632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3632
  · have he : independentCachedBranchMembers3634.filter (independentCachedEdge 2646)=independentCachedBranchMembers3633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3633
def independentCachedBranchMembers3635 : Finset ℕ := ([12,40,48,132,222,250,1594,1622,1628,1642,1650,1678,1686,1692,1714,1720,1734,1740,1748,1762,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3635 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3635 1692 5
  · have he : independentCachedBranchMembers3635.erase 1692=independentCachedBranchMembers3621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3621
  · have he : independentCachedBranchMembers3635.filter (independentCachedEdge 1692)=independentCachedBranchMembers3634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3634
def independentCachedBranchMembers3636 : Finset ℕ := ([40,250,1622,1628,1642,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2716,2730,2772,2792,3130,3150,3186,3192,3222,3242,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3636 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3636 5 (fun x => (if x<2674 then (if x<1714 then (if x<1628 then (if x<250 then 0 else (if x<1622 then 0 else 1)) else (if x<1642 then 2 else (if x<1678 then 0 else 1))) else (if x<1740 then (if x<1720 then 1 else (if x<1734 then 0 else 2)) else (if x<2618 then (if x<1776 then 3 else 2) else (if x<2638 then 0 else 1)))) else (if x<3150 then (if x<2730 then (if x<2680 then 1 else (if x<2716 then 2 else 3)) else (if x<2792 then (if x<2772 then 1 else 2) else (if x<3130 then 0 else 4))) else (if x<3222 then (if x<3186 then 4 else (if x<3192 then 3 else 0)) else (if x<3284 then (if x<3242 then 4 else 0) else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3637 : Finset ℕ := ([250,1622,1628,1714,1720,1776,2638,2730,2792,3150,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3637 4 (fun x => (if x<2638 then (if x<1714 then (if x<1622 then 0 else (if x<1628 then 1 else 2)) else (if x<1720 then 0 else (if x<1776 then 2 else 1))) else (if x<3150 then (if x<2730 then 1 else (if x<2792 then 0 else 1)) else (if x<3242 then 2 else (if x<3298 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3638 : Finset ℕ := ([40,132,250,1622,1628,1642,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2716,2730,2772,2792,3130,3150,3186,3192,3222,3242,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3638 132 4
  · have he : independentCachedBranchMembers3638.erase 132=independentCachedBranchMembers3636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3636
  · have he : independentCachedBranchMembers3638.filter (independentCachedEdge 132)=independentCachedBranchMembers3637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3637
def independentCachedBranchMembers3639 : Finset ℕ := ([1628,1720,1740,1776,2680,2716,2772,2792,3130,3150,3186,3222,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3639 4 (fun x => (if x<2792 then (if x<1776 then (if x<1720 then 0 else (if x<1740 then 0 else 1)) else (if x<2716 then (if x<2680 then 1 else 0) else (if x<2772 then 0 else 1))) else (if x<3186 then (if x<3130 then 1 else (if x<3150 then 2 else 2)) else (if x<3242 then (if x<3222 then 3 else 2) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3640 : Finset ℕ := ([1628,1740,2716,2772,3150,3222] : List ℕ).toFinset
theorem independentCachedBranchBound3640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3640 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3640 3 (fun x => (if x<2772 then (if x<1740 then 0 else (if x<2716 then 1 else 0)) else (if x<3150 then 1 else (if x<3222 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3641 : Finset ℕ := ([250,1628,1720,1740,1776,2680,2716,2772,2792,3130,3150,3186,3222,3242,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3641 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3641 250 3
  · have he : independentCachedBranchMembers3641.erase 250=independentCachedBranchMembers3639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3639
  · have he : independentCachedBranchMembers3641.filter (independentCachedEdge 250)=independentCachedBranchMembers3640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3640
def independentCachedBranchMembers3642 : Finset ℕ := ([40,132,250,1622,1628,1642,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2710,2716,2730,2772,2792,3130,3150,3186,3192,3222,3242,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3642 2710 4
  · have he : independentCachedBranchMembers3642.erase 2710=independentCachedBranchMembers3638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3638
  · have he : independentCachedBranchMembers3642.filter (independentCachedEdge 2710)=independentCachedBranchMembers3641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3641
def independentCachedBranchMembers3643 : Finset ℕ := ([250,1622,1714,1734,1776,2618,2638,2680,2716,2730,2792,3186,3222,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3643 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3643 4 (fun x => (if x<2680 then (if x<1734 then (if x<1622 then 0 else (if x<1714 then 1 else 0)) else (if x<2618 then (if x<1776 then 2 else 1) else (if x<2638 then 0 else 1))) else (if x<3186 then (if x<2730 then (if x<2716 then 2 else 3) else (if x<2792 then 3 else 1)) else (if x<3284 then (if x<3222 then 0 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3644 : Finset ℕ := ([1714,1776,2638,2716,3186,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3644 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3644 3 (fun x => (if x<2716 then (if x<1776 then 0 else (if x<2638 then 1 else 0)) else (if x<3186 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3645 : Finset ℕ := ([40,250,1622,1714,1734,1776,2618,2638,2680,2716,2730,2792,3186,3222,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3645 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3645 40 3
  · have he : independentCachedBranchMembers3645.erase 40=independentCachedBranchMembers3643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3643
  · have he : independentCachedBranchMembers3645.filter (independentCachedEdge 40)=independentCachedBranchMembers3644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3644
def independentCachedBranchMembers3646 : Finset ℕ := ([40,132,250,1622,1628,1642,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2710,2716,2730,2772,2792,3130,3150,3186,3192,3222,3228,3242,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3646 3228 4
  · have he : independentCachedBranchMembers3646.erase 3228=independentCachedBranchMembers3642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3642
  · have he : independentCachedBranchMembers3646.filter (independentCachedEdge 3228)=independentCachedBranchMembers3645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3645
def independentCachedBranchMembers3647 : Finset ℕ := ([40,132,1622,1678,1720,1740,2674,2716,2730,2792,3130,3150,3192,3222,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3647 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3647 4 (fun x => (if x<2730 then (if x<1720 then (if x<1622 then (if x<132 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2674 then (if x<1740 then 2 else 2) else (if x<2716 then 1 else 2))) else (if x<3192 then (if x<3130 then (if x<2792 then 1 else 2) else (if x<3150 then 0 else 3)) else (if x<3284 then (if x<3222 then 3 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3648 : Finset ℕ := ([40,132,250,1622,1628,1642,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2710,2716,2730,2772,2786,2792,3130,3150,3186,3192,3222,3228,3242,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3648 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3648 2786 4
  · have he : independentCachedBranchMembers3648.erase 2786=independentCachedBranchMembers3646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3646
  · have he : independentCachedBranchMembers3648.filter (independentCachedEdge 2786)=independentCachedBranchMembers3647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3647
def independentCachedBranchMembers3649 : Finset ℕ := ([12,40,48,132,222,250,1594,1614,1622,1628,1642,1650,1678,1686,1692,1714,1720,1734,1740,1748,1762,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3649 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3649 1614 5
  · have he : independentCachedBranchMembers3649.erase 1614=independentCachedBranchMembers3635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3635
  · have he : independentCachedBranchMembers3649.filter (independentCachedEdge 1614)=independentCachedBranchMembers3648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3648
def independentCachedBranchMembers3650 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1720,1734,1768,2638,2646,2680,2716,2730,2738,2764,2772,2786,3130,3164,3178,3186,3222,3256,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3650 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3650 5 (fun x => (if x<2680 then (if x<1650 then (if x<250 then (if x<48 then 0 else (if x<132 then 1 else 0)) else (if x<1628 then (if x<1594 then 1 else 0) else (if x<1642 then 2 else 2))) else (if x<1734 then (if x<1678 then 1 else (if x<1720 then 2 else 1)) else (if x<2638 then (if x<1768 then 3 else 3) else (if x<2646 then 2 else 3)))) else (if x<3130 then (if x<2738 then (if x<2716 then 0 else (if x<2730 then 2 else 2)) else (if x<2772 then (if x<2764 then 1 else 3) else (if x<2786 then 0 else 3))) else (if x<3222 then (if x<3178 then (if x<3164 then 1 else 4) else (if x<3186 then 0 else 4)) else (if x<3270 then (if x<3256 then 4 else 4) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3651 : Finset ℕ := ([40,250,1594,1628,1642,1678,1720,1768,2646,2738,2772,2786,3186,3222,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3651 4 (fun x => (if x<2646 then (if x<1642 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1720 then (if x<1678 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3186 then (if x<2772 then (if x<2738 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3270 then (if x<3222 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3652 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1720,1734,1768,2638,2646,2680,2716,2730,2738,2764,2772,2786,3130,3164,3178,3186,3214,3222,3256,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3652 3214 4
  · have he : independentCachedBranchMembers3652.erase 3214=independentCachedBranchMembers3650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3650
  · have he : independentCachedBranchMembers3652.filter (independentCachedEdge 3214)=independentCachedBranchMembers3651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3651
def independentCachedBranchMembers3653 : Finset ℕ := ([40,132,1650,1678,1720,1768,2646,2716,2730,2764,3130,3164,3178,3222,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3653 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3653 4 (fun x => (if x<2730 then (if x<1720 then (if x<1650 then (if x<132 then 0 else 0) else (if x<1678 then 1 else 2)) else (if x<2646 then (if x<1768 then 1 else 2) else (if x<2716 then 1 else 1))) else (if x<3178 then (if x<3130 then (if x<2764 then 2 else 2) else (if x<3164 then 0 else 3)) else (if x<3270 then (if x<3222 then 3 else 0) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3654 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1720,1734,1768,1776,2638,2646,2680,2716,2730,2738,2764,2772,2786,3130,3164,3178,3186,3214,3222,3256,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3654 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3654 1776 4
  · have he : independentCachedBranchMembers3654.erase 1776=independentCachedBranchMembers3652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3652
  · have he : independentCachedBranchMembers3654.filter (independentCachedEdge 1776)=independentCachedBranchMembers3653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3653
def independentCachedBranchMembers3655 : Finset ℕ := ([48,250,1642,1678,1734,1768,2638,2730,2764,2786,3130,3164,3186,3222,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3655 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3655 4 (fun x => (if x<2764 then (if x<1734 then (if x<1642 then (if x<250 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1768 then 2 else 2) else (if x<2730 then 1 else 1))) else (if x<3186 then (if x<3130 then (if x<2786 then 2 else 2) else (if x<3164 then 0 else 3)) else (if x<3256 then (if x<3222 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3656 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1720,1734,1768,1776,2638,2646,2680,2716,2730,2738,2764,2772,2786,3130,3164,3178,3186,3214,3222,3256,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3656 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3656 1686 4
  · have he : independentCachedBranchMembers3656.erase 1686=independentCachedBranchMembers3654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3654
  · have he : independentCachedBranchMembers3656.filter (independentCachedEdge 1686)=independentCachedBranchMembers3655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3655
def independentCachedBranchMembers3657 : Finset ℕ := ([12,40,48,132,222,250,1594,1614,1622,1628,1642,1650,1678,1686,1692,1714,1720,1734,1740,1748,1762,1768,1776,2618,2638,2646,2652,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3657 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3657 2652 5
  · have he : independentCachedBranchMembers3657.erase 2652=independentCachedBranchMembers3649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3649
  · have he : independentCachedBranchMembers3657.filter (independentCachedEdge 2652)=independentCachedBranchMembers3656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3656
def independentCachedBranchMembers3658 : Finset ℕ := ([12,48,132,222,1614,1650,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,2702,2716,2758,2792,3102,3158,3178,3192,3222,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3658 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3658 5 (fun x => (if x<2652 then (if x<1692 then (if x<222 then (if x<48 then 0 else (if x<132 then 0 else 1)) else (if x<1650 then (if x<1614 then 1 else 0) else (if x<1678 then 0 else 1))) else (if x<1748 then (if x<1714 then 2 else (if x<1734 then 2 else 2)) else (if x<2618 then (if x<1768 then 1 else 2) else (if x<2638 then 3 else 3)))) else (if x<3158 then (if x<2716 then (if x<2674 then 4 else (if x<2702 then 4 else 0)) else (if x<2792 then (if x<2758 then 1 else 1) else (if x<3102 then 3 else 3))) else (if x<3256 then (if x<3192 then (if x<3178 then 4 else 3) else (if x<3222 then 4 else 1)) else (if x<3298 then (if x<3276 then 2 else 0) else (if x<3312 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3659 : Finset ℕ := ([12,48,132,222,1614,1650,1692,1734,2638,2674,2716,2758,3158,3178,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3659 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3659 4 (fun x => (if x<2638 then (if x<1614 then (if x<132 then (if x<48 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1692 then (if x<1650 then 0 else 0) else (if x<1734 then 1 else 1))) else (if x<3158 then (if x<2716 then (if x<2674 then 2 else 2) else (if x<2758 then 3 else 3)) else (if x<3256 then (if x<3178 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3660 : Finset ℕ := ([12,48,132,222,1614,1650,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,2702,2716,2758,2792,3102,3158,3178,3192,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3660 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3660 3242 4
  · have he : independentCachedBranchMembers3660.erase 3242=independentCachedBranchMembers3658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3658
  · have he : independentCachedBranchMembers3660.filter (independentCachedEdge 3242)=independentCachedBranchMembers3659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3659
def independentCachedBranchMembers3661 : Finset ℕ := ([12,48,1614,1650,1678,1714,1748,1768,2618,2652,2716,2758,3102,3192,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3661 4 (fun x => (if x<2618 then (if x<1678 then (if x<1614 then (if x<48 then 0 else 0) else (if x<1650 then 0 else 0)) else (if x<1748 then (if x<1714 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3102 then (if x<2716 then (if x<2652 then 2 else 2) else (if x<2758 then 3 else 3)) else (if x<3256 then (if x<3192 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3662 : Finset ℕ := ([12,48,132,222,1614,1650,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,2702,2716,2758,2772,2792,3102,3158,3178,3192,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3662 2772 4
  · have he : independentCachedBranchMembers3662.erase 2772=independentCachedBranchMembers3660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3660
  · have he : independentCachedBranchMembers3662.filter (independentCachedEdge 2772)=independentCachedBranchMembers3661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3661
def independentCachedBranchMembers3663 : Finset ℕ := ([132,222,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,3102,3158,3178,3192] : List ℕ).toFinset
theorem independentCachedBranchBound3663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3663 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3663 4 (fun x => (if x<2618 then (if x<1714 then (if x<1678 then (if x<222 then 0 else 0) else (if x<1692 then 0 else 1)) else (if x<1748 then (if x<1734 then 1 else 1) else (if x<1768 then 0 else 1))) else (if x<3102 then (if x<2652 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3158 then 2 else 3) else (if x<3192 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3664 : Finset ℕ := ([12,48,132,222,1614,1650,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,2702,2716,2738,2758,2772,2792,3102,3158,3178,3192,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3664 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3664 2738 4
  · have he : independentCachedBranchMembers3664.erase 2738=independentCachedBranchMembers3662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3662
  · have he : independentCachedBranchMembers3664.filter (independentCachedEdge 2738)=independentCachedBranchMembers3663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3663
def independentCachedBranchMembers3665 : Finset ℕ := ([132,1614,1692,1714,1748,2618,2652,2674,2702,2758,2792,3178,3222,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3665 4 (fun x => (if x<2674 then (if x<1714 then (if x<1614 then 0 else (if x<1692 then 1 else 0)) else (if x<2618 then (if x<1748 then 2 else 1) else (if x<2652 then 2 else 1))) else (if x<3178 then (if x<2758 then (if x<2702 then 0 else 3) else (if x<2792 then 1 else 3)) else (if x<3256 then (if x<3222 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3666 : Finset ℕ := ([1692,1748,2652,2792,3178,3222] : List ℕ).toFinset
theorem independentCachedBranchBound3666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3666 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3666 3 (fun x => (if x<2792 then (if x<1748 then 0 else (if x<2652 then 1 else 0)) else (if x<3178 then 2 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3667 : Finset ℕ := ([48,132,1614,1692,1714,1748,2618,2652,2674,2702,2758,2792,3178,3222,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3667 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3667 48 3
  · have he : independentCachedBranchMembers3667.erase 48=independentCachedBranchMembers3665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3665
  · have he : independentCachedBranchMembers3667.filter (independentCachedEdge 48)=independentCachedBranchMembers3666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3666
def independentCachedBranchMembers3668 : Finset ℕ := ([12,48,132,222,1614,1628,1650,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,2702,2716,2738,2758,2772,2792,3102,3158,3178,3192,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3668 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3668 1628 4
  · have he : independentCachedBranchMembers3668.erase 1628=independentCachedBranchMembers3664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3664
  · have he : independentCachedBranchMembers3668.filter (independentCachedEdge 1628)=independentCachedBranchMembers3667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3667
def independentCachedBranchMembers3669 : Finset ℕ := ([222,1650,1714,1734,1748,2618,2638,2652,2702,2716,2792,3158,3222,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3669 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3669 4 (fun x => (if x<2652 then (if x<1734 then (if x<1650 then 0 else (if x<1714 then 1 else 2)) else (if x<2618 then (if x<1748 then 0 else 1) else (if x<2638 then 1 else 0))) else (if x<3158 then (if x<2716 then (if x<2702 then 2 else 3) else (if x<2792 then 1 else 3)) else (if x<3298 then (if x<3222 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3670 : Finset ℕ := ([1734,1748,2618,2792,3158,3222] : List ℕ).toFinset
theorem independentCachedBranchBound3670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3670 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3670 3 (fun x => (if x<2792 then (if x<1748 then 0 else (if x<2618 then 1 else 0)) else (if x<3158 then 2 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3671 : Finset ℕ := ([12,222,1650,1714,1734,1748,2618,2638,2652,2702,2716,2792,3158,3222,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3671 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3671 12 3
  · have he : independentCachedBranchMembers3671.erase 12=independentCachedBranchMembers3669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3669
  · have he : independentCachedBranchMembers3671.filter (independentCachedEdge 12)=independentCachedBranchMembers3670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3670
def independentCachedBranchMembers3672 : Finset ℕ := ([12,48,132,222,1594,1614,1628,1650,1678,1692,1714,1734,1748,1768,2618,2638,2652,2674,2702,2716,2738,2758,2772,2792,3102,3158,3178,3192,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3672 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3672 1594 4
  · have he : independentCachedBranchMembers3672.erase 1594=independentCachedBranchMembers3668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3668
  · have he : independentCachedBranchMembers3672.filter (independentCachedEdge 1594)=independentCachedBranchMembers3671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3671
def independentCachedBranchMembers3673 : Finset ℕ := ([12,40,48,132,222,250,1594,1614,1622,1628,1642,1650,1678,1686,1692,1714,1720,1734,1740,1748,1762,1768,1776,2618,2638,2646,2652,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3673 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3673 3304 5
  · have he : independentCachedBranchMembers3673.erase 3304=independentCachedBranchMembers3657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3657
  · have he : independentCachedBranchMembers3673.filter (independentCachedEdge 3304)=independentCachedBranchMembers3672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3672
def independentCachedBranchMembers3674 : Finset ℕ := ([12,18,36,40,48,66,72,80,130,132,144,192,222,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3674 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3674 36 6
  · have he : independentCachedBranchMembers3674.erase 36=independentCachedBranchMembers3500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3500
  · have he : independentCachedBranchMembers3674.filter (independentCachedEdge 36)=independentCachedBranchMembers3673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3673
def independentCachedBranchMembers3675 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2674,2680,2714,2738,2740,2770,2772,2776,3130,3158,3162,3188,3222,3228,3250,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3675 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3675 6 (fun x => (if x<2674 then (if x<1628 then (if x<246 then (if x<144 then (if x<80 then 0 else 1) else (if x<222 then 2 else 0)) else (if x<1590 then (if x<250 then 1 else 2) else (if x<1626 then 3 else 0))) else (if x<1720 then (if x<1686 then (if x<1650 then 3 else 1) else (if x<1690 then 0 else 2)) else (if x<1748 then (if x<1746 then 3 else 3) else (if x<1776 then 1 else (if x<2646 then 2 else 0))))) else (if x<3130 then (if x<2740 then (if x<2714 then (if x<2680 then 4 else 5) else (if x<2738 then 0 else 2)) else (if x<2772 then (if x<2770 then 4 else 1) else (if x<2776 then 5 else 2))) else (if x<3222 then (if x<3162 then (if x<3158 then 5 else 1) else (if x<3188 then 4 else 4)) else (if x<3250 then (if x<3228 then 5 else 4) else (if x<3282 then 3 else (if x<3288 then 0 else 3)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3676 : Finset ℕ := ([18,80,222,250,1628,1650,1690,1746,2646,2674,2680,2714,2740,2770,2776,3162,3188,3222,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3676 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3676 5 (fun x => (if x<2680 then (if x<1650 then (if x<222 then (if x<80 then 0 else 1) else (if x<250 then 0 else (if x<1628 then 1 else 2))) else (if x<1746 then (if x<1690 then 1 else 0) else (if x<2646 then 2 else (if x<2674 then 2 else 3)))) else (if x<3162 then (if x<2740 then (if x<2714 then 1 else 3) else (if x<2770 then 3 else (if x<2776 then 0 else 2))) else (if x<3222 then (if x<3188 then 0 else 3) else (if x<3228 then 0 else (if x<3250 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3677 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2674,2680,2714,2738,2740,2770,2772,2776,3130,3158,3162,3188,3222,3228,3250,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3677 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3677 3252 5
  · have he : independentCachedBranchMembers3677.erase 3252=independentCachedBranchMembers3675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3675
  · have he : independentCachedBranchMembers3677.filter (independentCachedEdge 3252)=independentCachedBranchMembers3676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3676
def independentCachedBranchMembers3678 : Finset ℕ := ([144,222,1628,1650,1686,1690,1720,1748,2674,2714,2740,2772,2776,3130,3158,3162,3188,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3678 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3678 5 (fun x => (if x<2740 then (if x<1690 then (if x<1628 then (if x<222 then 0 else 0) else (if x<1650 then 1 else (if x<1686 then 1 else 0))) else (if x<1748 then (if x<1720 then 1 else 2) else (if x<2674 then 2 else (if x<2714 then 3 else 0)))) else (if x<3162 then (if x<2776 then (if x<2772 then 2 else 0) else (if x<3130 then 2 else (if x<3158 then 3 else 3))) else (if x<3228 then (if x<3188 then 1 else 1) else (if x<3250 then 0 else (if x<3282 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3679 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2674,2680,2714,2738,2740,2770,2772,2776,3130,3158,3162,3186,3188,3222,3228,3250,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3679 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3679 3186 5
  · have he : independentCachedBranchMembers3679.erase 3186=independentCachedBranchMembers3677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3677
  · have he : independentCachedBranchMembers3679.filter (independentCachedEdge 3186)=independentCachedBranchMembers3678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3678
def independentCachedBranchMembers3680 : Finset ℕ := ([80,144,246,250,1650,1720,1746,1748,2674,2680,2738,2740,2770,2772,2776,3130,3158,3162,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound3680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3680 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3680 5 (fun x => (if x<2738 then (if x<1720 then (if x<246 then (if x<144 then 0 else 1) else (if x<250 then 0 else (if x<1650 then 1 else 0))) else (if x<1748 then (if x<1746 then 1 else 1) else (if x<2674 then 0 else (if x<2680 then 2 else 3)))) else (if x<3130 then (if x<2770 then (if x<2740 then 1 else 2) else (if x<2772 then 0 else (if x<2776 then 3 else 1))) else (if x<3162 then (if x<3158 then 3 else 0) else (if x<3222 then 2 else (if x<3228 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3681 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2674,2680,2714,2738,2740,2770,2772,2776,3102,3130,3158,3162,3186,3188,3222,3228,3250,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3681 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3681 3102 5
  · have he : independentCachedBranchMembers3681.erase 3102=independentCachedBranchMembers3679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3679
  · have he : independentCachedBranchMembers3681.filter (independentCachedEdge 3102)=independentCachedBranchMembers3680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3680
def independentCachedBranchMembers3682 : Finset ℕ := ([18,222,1590,1626,1628,1686,1690,1776,2674,2680,2738,2740,2770,2772,2776,3130,3158,3162,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound3682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3682 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3682 5 (fun x => (if x<2738 then (if x<1686 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1626 then 1 else (if x<1628 then 0 else 1))) else (if x<1776 then (if x<1690 then 0 else 1) else (if x<2674 then 1 else (if x<2680 then 2 else 3)))) else (if x<3130 then (if x<2770 then (if x<2740 then 1 else 2) else (if x<2772 then 0 else (if x<2776 then 3 else 1))) else (if x<3162 then (if x<3158 then 3 else 0) else (if x<3222 then 2 else (if x<3228 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3683 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2674,2680,2714,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3222,3228,3250,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3683 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3683 2800 5
  · have he : independentCachedBranchMembers3683.erase 2800=independentCachedBranchMembers3681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3681
  · have he : independentCachedBranchMembers3683.filter (independentCachedEdge 2800)=independentCachedBranchMembers3682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3682
def independentCachedBranchMembers3684 : Finset ℕ := ([18,80,246,250,1590,1626,1746,1776,2674,2714,2740,2772,2776,3130,3158,3162,3188,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound3684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3684 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3684 5 (fun x => (if x<2740 then (if x<1626 then (if x<246 then (if x<80 then 0 else 1) else (if x<250 then 0 else (if x<1590 then 1 else 0))) else (if x<1776 then (if x<1746 then 1 else 0) else (if x<2674 then 1 else (if x<2714 then 0 else 2)))) else (if x<3162 then (if x<2776 then (if x<2772 then 2 else 3) else (if x<3130 then 1 else (if x<3158 then 3 else 0))) else (if x<3228 then (if x<3188 then 2 else 2) else (if x<3250 then 2 else (if x<3282 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3685 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2674,2680,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3222,3228,3250,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3685 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3685 2716 5
  · have he : independentCachedBranchMembers3685.erase 2716=independentCachedBranchMembers3683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3683
  · have he : independentCachedBranchMembers3685.filter (independentCachedEdge 2716)=independentCachedBranchMembers3684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3684
def independentCachedBranchMembers3686 : Finset ℕ := ([144,246,1590,1626,1686,1720,1748,1776,2646,2674,2680,2714,2740,2770,2776,3162,3188,3222,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound3686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3686 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3686 5 (fun x => (if x<2680 then (if x<1720 then (if x<1590 then (if x<246 then 0 else 0) else (if x<1626 then 1 else (if x<1686 then 1 else 0))) else (if x<1776 then (if x<1748 then 1 else 1) else (if x<2646 then 0 else (if x<2674 then 1 else 2)))) else (if x<3162 then (if x<2740 then (if x<2714 then 3 else 2) else (if x<2770 then 0 else (if x<2776 then 0 else 1))) else (if x<3222 then (if x<3188 then 2 else 2) else (if x<3228 then 3 else (if x<3250 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3687 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2650,2674,2680,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3222,3228,3250,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3687 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3687 2650 5
  · have he : independentCachedBranchMembers3687.erase 2650=independentCachedBranchMembers3685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3685
  · have he : independentCachedBranchMembers3687.filter (independentCachedEdge 2650)=independentCachedBranchMembers3686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3686
def independentCachedBranchMembers3688 : Finset ℕ := ([18,250,1590,1626,1650,1690,1720,1748,2650,2674,2680,2714,2738,2772,3130,3158,3188,3222,3228,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3688 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3688 5 (fun x => (if x<2714 then (if x<1690 then (if x<1590 then (if x<250 then 0 else 0) else (if x<1626 then 1 else (if x<1650 then 0 else 2))) else (if x<2650 then (if x<1720 then 1 else (if x<1748 then 2 else 1)) else (if x<2674 then 3 else (if x<2680 then 0 else 2)))) else (if x<3188 then (if x<2772 then (if x<2738 then 0 else 2) else (if x<3130 then 3 else (if x<3158 then 0 else 3))) else (if x<3252 then (if x<3222 then 1 else (if x<3228 then 1 else 4)) else (if x<3282 then 3 else (if x<3288 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3689 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2650,2674,2680,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3222,3228,3250,3252,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3689 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3689 3284 5
  · have he : independentCachedBranchMembers3689.erase 3284=independentCachedBranchMembers3687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3687
  · have he : independentCachedBranchMembers3689.filter (independentCachedEdge 3284)=independentCachedBranchMembers3688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3688
def independentCachedBranchMembers3690 : Finset ℕ := ([18,144,222,246,1590,1690,1746,1748,2646,2680,2714,2716,2738,2740,2770,2772,3130,3162,3186,3188,3222,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3690 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3690 5 (fun x => (if x<2716 then (if x<1690 then (if x<222 then (if x<144 then 0 else 1) else (if x<246 then 0 else (if x<1590 then 1 else 2))) else (if x<2646 then (if x<1746 then 0 else (if x<1748 then 1 else 2)) else (if x<2680 then 2 else (if x<2714 then 3 else 3)))) else (if x<3130 then (if x<2740 then (if x<2738 then 4 else 1) else (if x<2770 then 2 else (if x<2772 then 0 else 1))) else (if x<3188 then (if x<3162 then 3 else (if x<3186 then 0 else 4)) else (if x<3222 then 2 else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3691 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2650,2674,2680,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3228,3250,3252,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3691 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3691 3192 5
  · have he : independentCachedBranchMembers3691.erase 3192=independentCachedBranchMembers3689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3689
  · have he : independentCachedBranchMembers3691.filter (independentCachedEdge 3192)=independentCachedBranchMembers3690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3690
def independentCachedBranchMembers3692 : Finset ℕ := ([80,250,1626,1628,1650,1686,1720,1776,2646,2680,2714,2716,2738,2740,2770,2772,3130,3162,3186,3188,3222,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3692 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3692 5 (fun x => (if x<2716 then (if x<1686 then (if x<1626 then (if x<250 then 0 else 0) else (if x<1628 then 0 else (if x<1650 then 1 else 1))) else (if x<2646 then (if x<1720 then 1 else (if x<1776 then 1 else 0)) else (if x<2680 then 1 else (if x<2714 then 0 else 2)))) else (if x<3130 then (if x<2740 then (if x<2738 then 1 else 1) else (if x<2770 then 2 else (if x<2772 then 0 else 3))) else (if x<3188 then (if x<3162 then 3 else (if x<3186 then 2 else 0)) else (if x<3222 then 2 else (if x<3288 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3693 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3228,3250,3252,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3693 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3693 2710 5
  · have he : independentCachedBranchMembers3693.erase 2710=independentCachedBranchMembers3691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3691
  · have he : independentCachedBranchMembers3693.filter (independentCachedEdge 2710)=independentCachedBranchMembers3692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3692
def independentCachedBranchMembers3694 : Finset ℕ := ([80,144,222,246,1628,1686,1746,1776,2650,2674,2680,2714,2738,2772,3130,3158,3188,3222,3228,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3694 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3694 5 (fun x => (if x<2714 then (if x<1686 then (if x<222 then (if x<144 then 0 else 1) else (if x<246 then 0 else (if x<1628 then 1 else 0))) else (if x<2650 then (if x<1746 then 1 else (if x<1776 then 0 else 1)) else (if x<2674 then 0 else (if x<2680 then 2 else 3)))) else (if x<3188 then (if x<2772 then (if x<2738 then 2 else 1) else (if x<3130 then 0 else (if x<3158 then 2 else 0))) else (if x<3252 then (if x<3222 then 2 else (if x<3228 then 3 else 2)) else (if x<3282 then 1 else (if x<3288 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3695 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3228,3250,3252,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3695 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3695 2618 5
  · have he : independentCachedBranchMembers3695.erase 2618=independentCachedBranchMembers3693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3693
  · have he : independentCachedBranchMembers3695.filter (independentCachedEdge 2618)=independentCachedBranchMembers3694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3694
def independentCachedBranchMembers3696 : Finset ℕ := ([18,222,1590,1626,1628,1686,1690,1776,2618,2646,2650,2710,2714,2716,2800,3102,3186,3188,3192,3250,3252,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3696 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3696 5 (fun x => (if x<2714 then (if x<1690 then (if x<1626 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 0 else (if x<1686 then 1 else 0))) else (if x<2646 then (if x<1776 then 1 else (if x<2618 then 1 else 2)) else (if x<2650 then 0 else (if x<2710 then 3 else 2)))) else (if x<3192 then (if x<3102 then (if x<2716 then 0 else (if x<2800 then 3 else 2)) else (if x<3186 then 0 else (if x<3188 then 3 else 1))) else (if x<3282 then (if x<3250 then 2 else (if x<3252 then 1 else 3)) else (if x<3284 then 0 else (if x<3288 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3697 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3228,3250,3252,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3697 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3697 3312 5
  · have he : independentCachedBranchMembers3697.erase 3312=independentCachedBranchMembers3695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3695
  · have he : independentCachedBranchMembers3697.filter (independentCachedEdge 3312)=independentCachedBranchMembers3696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3696
def independentCachedBranchMembers3698 : Finset ℕ := ([80,246,1590,1628,1650,1690,1748,1776,2646,2674,2680,2714,2740,2772,2800,3102,3130,3162,3188,3222,3228,3250,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3698 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3698 5 (fun x => (if x<2740 then (if x<1748 then (if x<1628 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1650 then 1 else (if x<1690 then 0 else 1))) else (if x<2674 then (if x<1776 then 0 else (if x<2646 then 1 else 0)) else (if x<2680 then 2 else (if x<2714 then 3 else 2)))) else (if x<3188 then (if x<3102 then (if x<2772 then 2 else (if x<2800 then 3 else 0)) else (if x<3130 then 1 else (if x<3162 then 3 else 2))) else (if x<3250 then (if x<3222 then 0 else (if x<3228 then 3 else 2)) else (if x<3282 then 1 else (if x<3288 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3699 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3226,3228,3250,3252,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3699 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3699 3226 5
  · have he : independentCachedBranchMembers3699.erase 3226=independentCachedBranchMembers3697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3697
  · have he : independentCachedBranchMembers3699.filter (independentCachedEdge 3226)=independentCachedBranchMembers3698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3698
def independentCachedBranchMembers3700 : Finset ℕ := ([18,80,222,246,1590,1626,1628,1650,1686,1720,1746,1748,2650,2674,2710,2770,2772,3130,3158,3192,3226,3228,3250,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3700 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3700 5 (fun x => (if x<2674 then (if x<1628 then (if x<246 then (if x<80 then 0 else (if x<222 then 1 else 0)) else (if x<1590 then 1 else (if x<1626 then 2 else 0))) else (if x<1720 then (if x<1650 then 2 else (if x<1686 then 1 else 0)) else (if x<1748 then (if x<1746 then 2 else 2) else (if x<2650 then 1 else 3)))) else (if x<3192 then (if x<2772 then (if x<2710 then 4 else (if x<2770 then 3 else 0)) else (if x<3130 then 4 else (if x<3158 then 4 else 0))) else (if x<3250 then (if x<3226 then 3 else (if x<3228 then 0 else 4)) else (if x<3288 then (if x<3252 then 2 else 3) else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3701 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3701 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3701 3256 5
  · have he : independentCachedBranchMembers3701.erase 3256=independentCachedBranchMembers3699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3699
  · have he : independentCachedBranchMembers3701.filter (independentCachedEdge 3256)=independentCachedBranchMembers3700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3700
def independentCachedBranchMembers3702 : Finset ℕ := ([18,246,1590,1626,1628,1690,1720,1746,1748,1776,2618,2646,2674,2710,2738,2740,2776,3102,3130,3158,3186,3188,3222,3250,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3702 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3702 5 (fun x => (if x<2710 then (if x<1720 then (if x<1626 then (if x<246 then 0 else (if x<1590 then 0 else 0)) else (if x<1628 then 1 else (if x<1690 then 2 else 2))) else (if x<1776 then (if x<1746 then 1 else (if x<1748 then 0 else 1)) else (if x<2646 then (if x<2618 then 2 else 1) else (if x<2674 then 0 else 3)))) else (if x<3158 then (if x<2776 then (if x<2738 then 3 else (if x<2740 then 0 else 1)) else (if x<3102 then 1 else (if x<3130 then 2 else 4))) else (if x<3222 then (if x<3186 then 3 else (if x<3188 then 0 else 2)) else (if x<3252 then (if x<3250 then 0 else 2) else (if x<3288 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3703 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1720,1746,1748,1752,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3703 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3703 1752 5
  · have he : independentCachedBranchMembers3703.erase 1752=independentCachedBranchMembers3701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3701
  · have he : independentCachedBranchMembers3703.filter (independentCachedEdge 1752)=independentCachedBranchMembers3702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3702
def independentCachedBranchMembers3704 : Finset ℕ := ([80,222,1628,1650,1686,1690,1720,1746,1776,2646,2650,2680,2716,2738,2772,2776,3102,3158,3162,3188,3192,3228,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3704 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3704 5 (fun x => (if x<2716 then (if x<1720 then (if x<1650 then (if x<222 then 0 else (if x<1628 then 0 else 0)) else (if x<1686 then 1 else (if x<1690 then 1 else 2))) else (if x<2646 then (if x<1746 then 1 else (if x<1776 then 0 else 2)) else (if x<2650 then 0 else (if x<2680 then 3 else 1)))) else (if x<3162 then (if x<2776 then (if x<2738 then 1 else (if x<2772 then 1 else 3)) else (if x<3102 then 0 else (if x<3158 then 2 else 3))) else (if x<3228 then (if x<3188 then 0 else (if x<3192 then 2 else 4)) else (if x<3284 then (if x<3250 then 4 else 2) else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3705 : Finset ℕ := ([80,222,1650,1686,2650,2680,2716,2772,3162,3192,3228,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3705 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3705 4 (fun x => (if x<2716 then (if x<1686 then (if x<222 then 0 else (if x<1650 then 0 else 1)) else (if x<2650 then 1 else (if x<2680 then 0 else 1))) else (if x<3192 then (if x<2772 then 1 else (if x<3162 then 0 else 2)) else (if x<3228 then 3 else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3706 : Finset ℕ := ([80,222,1590,1628,1650,1686,1690,1720,1746,1776,2646,2650,2680,2716,2738,2772,2776,3102,3158,3162,3188,3192,3228,3250,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3706 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3706 1590 4
  · have he : independentCachedBranchMembers3706.erase 1590=independentCachedBranchMembers3704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3704
  · have he : independentCachedBranchMembers3706.filter (independentCachedEdge 1590)=independentCachedBranchMembers3705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3705
def independentCachedBranchMembers3707 : Finset ℕ := ([18,80,144,222,246,250,1590,1626,1628,1650,1686,1690,1714,1720,1746,1748,1752,1776,2618,2646,2650,2674,2680,2710,2714,2716,2738,2740,2770,2772,2776,2800,3102,3130,3158,3162,3186,3188,3192,3222,3226,3228,3250,3252,3256,3282,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3707 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3707 1714 5
  · have he : independentCachedBranchMembers3707.erase 1714=independentCachedBranchMembers3703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3703
  · have he : independentCachedBranchMembers3707.filter (independentCachedEdge 1714)=independentCachedBranchMembers3706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3706
def independentCachedBranchMembers3708 : Finset ℕ := ([18,144,222,250,1590,1628,1650,1690,1748,1776,2618,2716,2738,2770,2776,3102,3130,3162,3188,3222,3228,3250,3256,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3708 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3708 5 (fun x => (if x<2738 then (if x<1650 then (if x<250 then (if x<144 then 0 else (if x<222 then 1 else 0)) else (if x<1590 then 1 else (if x<1628 then 2 else 2))) else (if x<1776 then (if x<1690 then 3 else (if x<1748 then 0 else 3)) else (if x<2618 then 1 else (if x<2716 then 3 else 3)))) else (if x<3188 then (if x<3102 then (if x<2770 then 1 else (if x<2776 then 0 else 1)) else (if x<3130 then 2 else (if x<3162 then 4 else 0))) else (if x<3250 then (if x<3222 then 2 else (if x<3228 then 0 else 4)) else (if x<3282 then (if x<3256 then 2 else 1) else (if x<3288 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3709 : Finset ℕ := ([250,1628,1650,1776,2716,2738,2770,3130,3162,3188,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3709 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3709 4 (fun x => (if x<2770 then (if x<1776 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<2716 then 1 else (if x<2738 then 2 else 0))) else (if x<3188 then (if x<3130 then 2 else (if x<3162 then 0 else 3)) else (if x<3256 then (if x<3222 then 1 else 2) else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3710 : Finset ℕ := ([18,144,222,250,1590,1628,1650,1690,1748,1776,2618,2710,2716,2738,2770,2776,3102,3130,3162,3188,3222,3228,3250,3256,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound3710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3710 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3710 2710 4
  · have he : independentCachedBranchMembers3710.erase 2710=independentCachedBranchMembers3708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3708
  · have he : independentCachedBranchMembers3710.filter (independentCachedEdge 2710)=independentCachedBranchMembers3709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3709
def independentCachedBranchMembers3711 : Finset ℕ := ([144,1590,1748,1776,2618,2770,2776,3162,3188,3222,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3711 4 (fun x => (if x<2776 then (if x<1776 then (if x<1590 then 0 else (if x<1748 then 1 else 0)) else (if x<2618 then 1 else (if x<2770 then 2 else 0))) else (if x<3222 then (if x<3162 then 1 else (if x<3188 then 2 else 3)) else (if x<3250 then 0 else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
