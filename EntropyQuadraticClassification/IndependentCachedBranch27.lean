/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch26
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers3456 : Finset ℕ := ([1652,1764,2606,2714,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3456 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3456 3 (fun x => (if x<2714 then (if x<1764 then 0 else (if x<2606 then 1 else 2)) else (if x<3284 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3457 : Finset ℕ := ([72,252,1652,1686,1714,1764,2606,2652,2680,2714,2764,2792,3126,3238,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3457 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3457 72 3
  · have he : independentCachedBranchMembers3457.erase 72=independentCachedBranchMembers3455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3455
  · have he : independentCachedBranchMembers3457.filter (independentCachedEdge 72)=independentCachedBranchMembers3456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3456
def independentCachedBranchMembers3458 : Finset ℕ := ([72,80,192,252,1594,1644,1652,1678,1686,1714,1752,1764,2606,2614,2652,2680,2714,2764,2772,2792,2800,3118,3126,3164,3192,3226,3238,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3458 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3458 3118 4
  · have he : independentCachedBranchMembers3458.erase 3118=independentCachedBranchMembers3454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3454
  · have he : independentCachedBranchMembers3458.filter (independentCachedEdge 3118)=independentCachedBranchMembers3457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3457
def independentCachedBranchMembers3459 : Finset ℕ := ([18,72,80,130,192,252,1590,1594,1628,1644,1652,1678,1686,1690,1702,1714,1740,1748,1752,1764,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3459 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3459 1690 5
  · have he : independentCachedBranchMembers3459.erase 1690=independentCachedBranchMembers3439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3439
  · have he : independentCachedBranchMembers3459.filter (independentCachedEdge 1690)=independentCachedBranchMembers3458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3458
def independentCachedBranchMembers3460 : Finset ℕ := ([18,72,252,1590,1594,1644,1678,1702,1748,1752,1776,2606,2652,2680,2710,2714,2764,2788,2792,3118,3188,3192,3222,3250,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3460 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3460 5 (fun x => (if x<2680 then (if x<1678 then (if x<1590 then (if x<72 then 0 else (if x<252 then 0 else 1)) else (if x<1594 then 0 else (if x<1644 then 2 else 0))) else (if x<1752 then (if x<1702 then 2 else (if x<1748 then 3 else 1)) else (if x<2606 then (if x<1776 then 2 else 3) else (if x<2652 then 2 else 1)))) else (if x<3188 then (if x<2764 then (if x<2710 then 2 else (if x<2714 then 0 else 2)) else (if x<2792 then (if x<2788 then 0 else 1) else (if x<3118 then 4 else 3))) else (if x<3250 then (if x<3192 then 1 else (if x<3222 then 3 else 4)) else (if x<3300 then (if x<3276 then 0 else 1) else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3461 : Finset ℕ := ([252,1678,1748,1752,2652,2714,2764,3118,3188,3192,3250,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3461 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3461 4 (fun x => (if x<2764 then (if x<1752 then (if x<1678 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then 1 else (if x<2714 then 0 else 1))) else (if x<3192 then (if x<3118 then 1 else (if x<3188 then 2 else 0)) else (if x<3300 then (if x<3250 then 2 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3462 : Finset ℕ := ([252,1752,2714,3118,3188,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3462 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3462 3 (fun x => (if x<3118 then (if x<1752 then 0 else (if x<2714 then 0 else 1)) else (if x<3188 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3463 : Finset ℕ := ([252,1678,1748,1752,2652,2710,2714,2764,3118,3188,3192,3250,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3463 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3463 2710 3
  · have he : independentCachedBranchMembers3463.erase 2710=independentCachedBranchMembers3461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3461
  · have he : independentCachedBranchMembers3463.filter (independentCachedEdge 2710)=independentCachedBranchMembers3462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3462
def independentCachedBranchMembers3464 : Finset ℕ := ([18,72,252,1590,1594,1644,1678,1702,1748,1752,1776,2606,2652,2680,2710,2714,2738,2764,2788,2792,3118,3188,3192,3222,3250,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3464 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3464 2738 4
  · have he : independentCachedBranchMembers3464.erase 2738=independentCachedBranchMembers3460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3460
  · have he : independentCachedBranchMembers3464.filter (independentCachedEdge 2738)=independentCachedBranchMembers3463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3463
def independentCachedBranchMembers3465 : Finset ℕ := ([18,1590,1594,1678,1776,2606,2652,2710,2714,2788,2792,3188,3192,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3465 4 (fun x => (if x<2710 then (if x<1678 then (if x<1590 then 0 else (if x<1594 then 0 else 1)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2652 then 1 else 3))) else (if x<3188 then (if x<2788 then (if x<2714 then 0 else 1) else (if x<2792 then 2 else 3)) else (if x<3250 then (if x<3192 then 2 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3466 : Finset ℕ := ([18,72,252,1590,1594,1644,1678,1702,1748,1752,1776,2606,2652,2680,2710,2714,2738,2764,2788,2792,3118,3164,3188,3192,3222,3250,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3466 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3466 3164 4
  · have he : independentCachedBranchMembers3466.erase 3164=independentCachedBranchMembers3464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3464
  · have he : independentCachedBranchMembers3466.filter (independentCachedEdge 3164)=independentCachedBranchMembers3465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3465
def independentCachedBranchMembers3467 : Finset ℕ := ([252,1590,1594,1748,1752,1776,2606,2764,2788,2792,3118,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3467 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3467 4 (fun x => (if x<2764 then (if x<1748 then (if x<1590 then 0 else (if x<1594 then 1 else 2)) else (if x<1776 then (if x<1752 then 0 else 2) else (if x<2606 then 1 else 1))) else (if x<3118 then (if x<2788 then 0 else (if x<2792 then 3 else 1)) else (if x<3300 then (if x<3276 then 2 else 2) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3468 : Finset ℕ := ([252,1748,1752,1776,2606,3118] : List ℕ).toFinset
theorem independentCachedBranchBound3468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3468 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3468 3 (fun x => (if x<1776 then (if x<1748 then 0 else (if x<1752 then 0 else 1)) else (if x<2606 then 2 else (if x<3118 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3469 : Finset ℕ := ([18,252,1590,1594,1748,1752,1776,2606,2764,2788,2792,3118,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3469 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3469 18 3
  · have he : independentCachedBranchMembers3469.erase 18=independentCachedBranchMembers3467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3467
  · have he : independentCachedBranchMembers3469.filter (independentCachedEdge 18)=independentCachedBranchMembers3468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3468
def independentCachedBranchMembers3470 : Finset ℕ := ([18,72,130,252,1590,1594,1644,1678,1702,1748,1752,1776,2606,2652,2680,2710,2714,2738,2764,2788,2792,3118,3164,3188,3192,3222,3250,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3470 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3470 130 4
  · have he : independentCachedBranchMembers3470.erase 130=independentCachedBranchMembers3466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3466
  · have he : independentCachedBranchMembers3470.filter (independentCachedEdge 130)=independentCachedBranchMembers3469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3469
def independentCachedBranchMembers3471 : Finset ℕ := ([252,1590,1702,1748,1776,2606,2652,2680,2714,2764,2792,3188,3222,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3471 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3471 4 (fun x => (if x<2680 then (if x<1748 then (if x<1590 then 0 else (if x<1702 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2652 then 1 else 0))) else (if x<3188 then (if x<2764 then (if x<2714 then 2 else 3) else (if x<2792 then 3 else 1)) else (if x<3250 then (if x<3222 then 0 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3472 : Finset ℕ := ([1748,1776,2606,2714,3188,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3472 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3472 3 (fun x => (if x<2714 then (if x<1776 then 0 else (if x<2606 then 1 else 0)) else (if x<3188 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3473 : Finset ℕ := ([72,252,1590,1702,1748,1776,2606,2652,2680,2714,2764,2792,3188,3222,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound3473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3473 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3473 72 3
  · have he : independentCachedBranchMembers3473.erase 72=independentCachedBranchMembers3471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3471
  · have he : independentCachedBranchMembers3473.filter (independentCachedEdge 72)=independentCachedBranchMembers3472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3472
def independentCachedBranchMembers3474 : Finset ℕ := ([18,72,130,252,1590,1594,1644,1678,1702,1748,1752,1776,2606,2652,2680,2710,2714,2738,2764,2788,2792,3118,3164,3188,3192,3222,3226,3250,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound3474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3474 3226 4
  · have he : independentCachedBranchMembers3474.erase 3226=independentCachedBranchMembers3470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3470
  · have he : independentCachedBranchMembers3474.filter (independentCachedEdge 3226)=independentCachedBranchMembers3473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3473
def independentCachedBranchMembers3475 : Finset ℕ := ([18,72,80,130,192,252,1582,1590,1594,1628,1644,1652,1678,1686,1690,1702,1714,1740,1748,1752,1764,1768,1776,2606,2614,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3475 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3475 1582 5
  · have he : independentCachedBranchMembers3475.erase 1582=independentCachedBranchMembers3459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3459
  · have he : independentCachedBranchMembers3475.filter (independentCachedEdge 1582)=independentCachedBranchMembers3474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3474
def independentCachedBranchMembers3476 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1752,1768,2606,2614,2680,2714,2730,2738,2764,2772,2788,3130,3164,3180,3188,3222,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3476 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3476 5 (fun x => (if x<2680 then (if x<1652 then (if x<252 then (if x<80 then 0 else (if x<130 then 1 else 0)) else (if x<1628 then (if x<1594 then 1 else 2) else (if x<1644 then 0 else 2))) else (if x<1752 then (if x<1678 then 1 else (if x<1702 then 2 else 3)) else (if x<2606 then (if x<1768 then 1 else 3) else (if x<2614 then 2 else 3)))) else (if x<3130 then (if x<2738 then (if x<2714 then 0 else (if x<2730 then 2 else 3)) else (if x<2772 then (if x<2764 then 0 else 2) else (if x<2788 then 1 else 3))) else (if x<3222 then (if x<3180 then (if x<3164 then 4 else 1) else (if x<3188 then 0 else 4)) else (if x<3288 then (if x<3238 then 4 else 0) else (if x<3312 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3477 : Finset ℕ := ([80,130,1594,1628,1652,1678,1702,1768,2606,2714,2738,2772,3180,3222,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3477 4 (fun x => (if x<2606 then (if x<1652 then (if x<1594 then (if x<130 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1702 then (if x<1678 then 1 else 0) else (if x<1768 then 1 else 1))) else (if x<3180 then (if x<2738 then (if x<2714 then 2 else 2) else (if x<2772 then 3 else 3)) else (if x<3288 then (if x<3222 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3478 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1752,1768,2606,2614,2680,2714,2730,2738,2764,2772,2788,3130,3164,3180,3188,3222,3238,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3478 3304 4
  · have he : independentCachedBranchMembers3478.erase 3304=independentCachedBranchMembers3476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3476
  · have he : independentCachedBranchMembers3478.filter (independentCachedEdge 3304)=independentCachedBranchMembers3477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3477
def independentCachedBranchMembers3479 : Finset ℕ := ([72,130,1652,1678,1752,1768,2614,2714,2730,2764,3130,3164,3180,3222,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3479 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3479 4 (fun x => (if x<2730 then (if x<1752 then (if x<1652 then (if x<130 then 0 else 0) else (if x<1678 then 1 else 2)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2714 then 1 else 1))) else (if x<3180 then (if x<3130 then (if x<2764 then 2 else 2) else (if x<3164 then 3 else 0)) else (if x<3238 then (if x<3222 then 3 else 0) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3480 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1702,1752,1768,1776,2606,2614,2680,2714,2730,2738,2764,2772,2788,3130,3164,3180,3188,3222,3238,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3480 1776 4
  · have he : independentCachedBranchMembers3480.erase 1776=independentCachedBranchMembers3478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3478
  · have he : independentCachedBranchMembers3480.filter (independentCachedEdge 1776)=independentCachedBranchMembers3479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3479
def independentCachedBranchMembers3481 : Finset ℕ := ([80,252,1644,1678,1702,1768,2606,2730,2764,2788,3130,3164,3188,3222,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3481 4 (fun x => (if x<2764 then (if x<1702 then (if x<1644 then (if x<252 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2606 then (if x<1768 then 2 else 2) else (if x<2730 then 1 else 2))) else (if x<3188 then (if x<3130 then (if x<2788 then 1 else 2) else (if x<3164 then 3 else 0)) else (if x<3288 then (if x<3222 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3482 : Finset ℕ := ([72,80,130,252,1594,1628,1644,1652,1678,1686,1702,1752,1768,1776,2606,2614,2680,2714,2730,2738,2764,2772,2788,3130,3164,3180,3188,3222,3238,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3482 1686 4
  · have he : independentCachedBranchMembers3482.erase 1686=independentCachedBranchMembers3480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3480
  · have he : independentCachedBranchMembers3482.filter (independentCachedEdge 1686)=independentCachedBranchMembers3481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3481
def independentCachedBranchMembers3483 : Finset ℕ := ([18,72,80,130,192,252,1582,1590,1594,1628,1644,1652,1678,1686,1690,1702,1714,1740,1748,1752,1764,1768,1776,2606,2614,2618,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3483 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3483 2618 5
  · have he : independentCachedBranchMembers3483.erase 2618=independentCachedBranchMembers3475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3475
  · have he : independentCachedBranchMembers3483.filter (independentCachedEdge 2618)=independentCachedBranchMembers3482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3482
def independentCachedBranchMembers3484 : Finset ℕ := ([18,72,192,252,1590,1644,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,2702,2776,2788,2792,3102,3118,3188,3192,3222,3226,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3484 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3484 5 (fun x => (if x<2652 then (if x<1714 then (if x<252 then (if x<72 then 0 else (if x<192 then 0 else 1)) else (if x<1644 then (if x<1590 then 1 else 0) else (if x<1678 then 0 else 2))) else (if x<1764 then (if x<1748 then 2 else (if x<1752 then 1 else 2)) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2618 then 3 else 4)))) else (if x<3118 then (if x<2776 then (if x<2668 then 3 else (if x<2702 then 4 else 3)) else (if x<2792 then (if x<2788 then 1 else 1) else (if x<3102 then 0 else 3))) else (if x<3226 then (if x<3192 then (if x<3188 then 4 else 3) else (if x<3222 then 4 else 0)) else (if x<3276 then (if x<3238 then 2 else 2) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3485 : Finset ℕ := ([18,72,192,252,1590,1644,1752,1764,2614,2668,2776,2788,3118,3188,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3485 4 (fun x => (if x<2614 then (if x<1590 then (if x<192 then (if x<72 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1752 then (if x<1644 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3118 then (if x<2776 then (if x<2668 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3188 then 2 else 2) else (if x<3238 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3486 : Finset ℕ := ([18,72,192,252,1590,1644,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,2702,2776,2788,2792,3102,3118,3188,3192,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3486 3242 4
  · have he : independentCachedBranchMembers3486.erase 3242=independentCachedBranchMembers3484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3484
  · have he : independentCachedBranchMembers3486.filter (independentCachedEdge 3242)=independentCachedBranchMembers3485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3485
def independentCachedBranchMembers3487 : Finset ℕ := ([18,72,1590,1644,1678,1714,1748,1768,2618,2652,2776,2788,3102,3192,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound3487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3487 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3487 4 (fun x => (if x<2618 then (if x<1678 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1644 then 0 else 0)) else (if x<1748 then (if x<1714 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3102 then (if x<2776 then (if x<2652 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3226 then (if x<3192 then 2 else 2) else (if x<3238 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3488 : Finset ℕ := ([18,72,192,252,1590,1644,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,2702,2772,2776,2788,2792,3102,3118,3188,3192,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3488 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3488 2772 4
  · have he : independentCachedBranchMembers3488.erase 2772=independentCachedBranchMembers3486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3486
  · have he : independentCachedBranchMembers3488.filter (independentCachedEdge 2772)=independentCachedBranchMembers3487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3487
def independentCachedBranchMembers3489 : Finset ℕ := ([192,252,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,3102,3118,3188,3192] : List ℕ).toFinset
theorem independentCachedBranchBound3489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3489 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3489 4 (fun x => (if x<2614 then (if x<1748 then (if x<1678 then (if x<252 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1764 then (if x<1752 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3102 then (if x<2652 then (if x<2618 then 2 else 3) else (if x<2668 then 2 else 3)) else (if x<3188 then (if x<3118 then 2 else 3) else (if x<3192 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3490 : Finset ℕ := ([18,72,192,252,1590,1644,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,2702,2738,2772,2776,2788,2792,3102,3118,3188,3192,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3490 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3490 2738 4
  · have he : independentCachedBranchMembers3490.erase 2738=independentCachedBranchMembers3488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3488
  · have he : independentCachedBranchMembers3490.filter (independentCachedEdge 2738)=independentCachedBranchMembers3489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3489
def independentCachedBranchMembers3491 : Finset ℕ := ([192,1644,1714,1748,1752,2614,2618,2652,2702,2788,2792,3118,3222,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3491 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3491 4 (fun x => (if x<2652 then (if x<1748 then (if x<1644 then 0 else (if x<1714 then 1 else 2)) else (if x<2614 then (if x<1752 then 0 else 1) else (if x<2618 then 2 else 0))) else (if x<3118 then (if x<2788 then (if x<2702 then 1 else 3) else (if x<2792 then 3 else 1)) else (if x<3226 then (if x<3222 then 0 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3492 : Finset ℕ := ([1748,1752,2652,2702,3118,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3492 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3492 3 (fun x => (if x<2702 then (if x<1752 then 0 else (if x<2652 then 1 else 0)) else (if x<3118 then 2 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3493 : Finset ℕ := ([18,192,1644,1714,1748,1752,2614,2618,2652,2702,2788,2792,3118,3222,3226,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3493 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3493 18 3
  · have he : independentCachedBranchMembers3493.erase 18=independentCachedBranchMembers3491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3491
  · have he : independentCachedBranchMembers3493.filter (independentCachedEdge 18)=independentCachedBranchMembers3492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3492
def independentCachedBranchMembers3494 : Finset ℕ := ([18,72,192,252,1590,1628,1644,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,2702,2738,2772,2776,2788,2792,3102,3118,3188,3192,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3494 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3494 1628 4
  · have he : independentCachedBranchMembers3494.erase 1628=independentCachedBranchMembers3490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3490
  · have he : independentCachedBranchMembers3494.filter (independentCachedEdge 1628)=independentCachedBranchMembers3493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3493
def independentCachedBranchMembers3495 : Finset ℕ := ([252,1590,1714,1748,1764,2618,2652,2668,2702,2776,2792,3188,3222,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3495 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3495 4 (fun x => (if x<2668 then (if x<1748 then (if x<1590 then 0 else (if x<1714 then 1 else 2)) else (if x<2618 then (if x<1764 then 0 else 1) else (if x<2652 then 1 else 0))) else (if x<3188 then (if x<2776 then (if x<2702 then 2 else 3) else (if x<2792 then 3 else 1)) else (if x<3238 then (if x<3222 then 0 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3496 : Finset ℕ := ([1748,1764,2618,2702,3188,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3496 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3496 3 (fun x => (if x<2702 then (if x<1764 then 0 else (if x<2618 then 1 else 0)) else (if x<3188 then 2 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3497 : Finset ℕ := ([72,252,1590,1714,1748,1764,2618,2652,2668,2702,2776,2792,3188,3222,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3497 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3497 72 3
  · have he : independentCachedBranchMembers3497.erase 72=independentCachedBranchMembers3495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3495
  · have he : independentCachedBranchMembers3497.filter (independentCachedEdge 72)=independentCachedBranchMembers3496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3496
def independentCachedBranchMembers3498 : Finset ℕ := ([18,72,192,252,1590,1594,1628,1644,1678,1714,1748,1752,1764,1768,2614,2618,2652,2668,2702,2738,2772,2776,2788,2792,3102,3118,3188,3192,3222,3226,3238,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3498 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3498 1594 4
  · have he : independentCachedBranchMembers3498.erase 1594=independentCachedBranchMembers3494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3494
  · have he : independentCachedBranchMembers3498.filter (independentCachedEdge 1594)=independentCachedBranchMembers3497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3497
def independentCachedBranchMembers3499 : Finset ℕ := ([18,72,80,130,192,252,1582,1590,1594,1628,1644,1652,1678,1686,1690,1702,1714,1740,1748,1752,1764,1768,1776,2606,2614,2618,2652,2668,2680,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3499 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3499 3214 5
  · have he : independentCachedBranchMembers3499.erase 3214=independentCachedBranchMembers3483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3483
  · have he : independentCachedBranchMembers3499.filter (independentCachedEdge 3214)=independentCachedBranchMembers3498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3498
def independentCachedBranchMembers3500 : Finset ℕ := ([12,18,40,48,66,72,80,130,132,144,192,222,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3500 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3500 66 6
  · have he : independentCachedBranchMembers3500.erase 66=independentCachedBranchMembers3320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3320
  · have he : independentCachedBranchMembers3500.filter (independentCachedEdge 66)=independentCachedBranchMembers3499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3499
def independentCachedBranchMembers3501 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1720,1734,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3178,3186,3192,3250,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3501 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3501 6 (fun x => (if x<2680 then (if x<1650 then (if x<250 then (if x<48 then 0 else (if x<132 then 1 else 0)) else (if x<1628 then (if x<1594 then 1 else 0) else (if x<1642 then 2 else 2))) else (if x<1768 then (if x<1720 then (if x<1678 then 1 else 2) else (if x<1734 then 1 else 3)) else (if x<2638 then (if x<2618 then 3 else 1) else (if x<2646 then 2 else 3)))) else (if x<3102 then (if x<2730 then (if x<2710 then 0 else (if x<2716 then 4 else 2)) else (if x<2786 then (if x<2764 then 2 else 3) else (if x<2800 then 3 else 1))) else (if x<3250 then (if x<3186 then (if x<3178 then 4 else 0) else (if x<3192 then 5 else 1)) else (if x<3270 then (if x<3256 then 1 else 5) else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3502 : Finset ℕ := ([40,250,1642,1720,2646,2680,2710,2730,2764,2786,2800,3186,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3502 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3502 5 (fun x => (if x<2730 then (if x<1720 then (if x<250 then 0 else (if x<1642 then 0 else 0)) else (if x<2680 then (if x<2646 then 0 else 1) else (if x<2710 then 0 else 2))) else (if x<3186 then (if x<2786 then (if x<2764 then 0 else 1) else (if x<2800 then 1 else 2)) else (if x<3270 then (if x<3250 then 1 else 2) else (if x<3284 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3503 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1720,1734,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3178,3186,3192,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3503 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3503 3276 5
  · have he : independentCachedBranchMembers3503.erase 3276=independentCachedBranchMembers3501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3501
  · have he : independentCachedBranchMembers3503.filter (independentCachedEdge 3276)=independentCachedBranchMembers3502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3502
def independentCachedBranchMembers3504 : Finset ℕ := ([48,132,1650,1734,2638,2680,2710,2716,2730,2764,2800,3178,3250,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3504 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3504 5 (fun x => (if x<2716 then (if x<1734 then (if x<132 then 0 else (if x<1650 then 0 else 0)) else (if x<2680 then (if x<2638 then 0 else 1) else (if x<2710 then 0 else 1))) else (if x<3178 then (if x<2764 then (if x<2730 then 2 else 1) else (if x<2800 then 0 else 2)) else (if x<3256 then (if x<3250 then 1 else 1) else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3505 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1720,1734,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3178,3186,3192,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3505 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3505 3242 5
  · have he : independentCachedBranchMembers3505.erase 3242=independentCachedBranchMembers3503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3503
  · have he : independentCachedBranchMembers3505.filter (independentCachedEdge 3242)=independentCachedBranchMembers3504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3504
def independentCachedBranchMembers3506 : Finset ℕ := ([48,250,1594,1628,1642,1734,2638,2680,2786,3102,3186,3192,3250,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3506 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3506 5 (fun x => (if x<2680 then (if x<1628 then (if x<250 then 0 else (if x<1594 then 0 else 0)) else (if x<1734 then (if x<1642 then 1 else 1) else (if x<2638 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2786 then 0 else 1) else (if x<3186 then 2 else 0)) else (if x<3256 then (if x<3250 then 2 else 2) else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3507 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1720,1734,1748,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3178,3186,3192,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3507 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3507 1748 5
  · have he : independentCachedBranchMembers3507.erase 1748=independentCachedBranchMembers3505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3505
  · have he : independentCachedBranchMembers3507.filter (independentCachedEdge 1748)=independentCachedBranchMembers3506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3506
def independentCachedBranchMembers3508 : Finset ℕ := ([40,132,1594,1628,1650,1720,2646,2680,2716,3102,3178,3192,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3508 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3508 5 (fun x => (if x<2680 then (if x<1628 then (if x<132 then 0 else (if x<1594 then 0 else 0)) else (if x<1720 then (if x<1650 then 1 else 1) else (if x<2646 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2716 then 0 else 1) else (if x<3178 then 2 else 0)) else (if x<3270 then (if x<3250 then 2 else 2) else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3509 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3178,3186,3192,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3509 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3509 1714 5
  · have he : independentCachedBranchMembers3509.erase 1714=independentCachedBranchMembers3507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3507
  · have he : independentCachedBranchMembers3509.filter (independentCachedEdge 1714)=independentCachedBranchMembers3508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3508
def independentCachedBranchMembers3510 : Finset ℕ := ([40,250,1594,1628,1642,1678,1714,1720,1748,1768,2618,2646,2786,3102,3186,3192,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3510 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3510 5 (fun x => (if x<1768 then (if x<1642 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1714 then (if x<1678 then 1 else 1) else (if x<1720 then 2 else (if x<1748 then 1 else 2)))) else (if x<3186 then (if x<2646 then (if x<2618 then 0 else 2) else (if x<2786 then 3 else (if x<3102 then 3 else 3))) else (if x<3242 then (if x<3192 then 3 else 0) else (if x<3270 then 0 else (if x<3276 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3511 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3178,3186,3192,3214,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3511 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3511 3214 5
  · have he : independentCachedBranchMembers3511.erase 3214=independentCachedBranchMembers3509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3509
  · have he : independentCachedBranchMembers3511.filter (independentCachedEdge 3214)=independentCachedBranchMembers3510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3510
def independentCachedBranchMembers3512 : Finset ℕ := ([40,48,132,1594,1678,1720,1748,2618,2638,2646,2680,2710,2764,2786,3102,3178,3186,3242,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3512 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3512 5 (fun x => (if x<2680 then (if x<1720 then (if x<132 then (if x<48 then 0 else 1) else (if x<1594 then 0 else (if x<1678 then 0 else 1))) else (if x<2618 then (if x<1748 then 1 else 2) else (if x<2638 then 2 else (if x<2646 then 1 else 2)))) else (if x<3178 then (if x<2764 then (if x<2710 then 0 else 3) else (if x<2786 then 3 else (if x<3102 then 3 else 4))) else (if x<3242 then (if x<3186 then 0 else 4) else (if x<3250 then 2 else (if x<3270 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3513 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3178,3186,3192,3214,3242,3250,3256,3270,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3513 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3513 3298 5
  · have he : independentCachedBranchMembers3513.erase 3298=independentCachedBranchMembers3511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3511
  · have he : independentCachedBranchMembers3513.filter (independentCachedEdge 3298)=independentCachedBranchMembers3512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3512
def independentCachedBranchMembers3514 : Finset ℕ := ([48,132,250,1594,1642,1678,1714,2618,2646,2680,2716,2764,2786,2800,3102,3186,3242,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3514 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3514 5 (fun x => (if x<2716 then (if x<1678 then (if x<250 then (if x<132 then 0 else 0) else (if x<1594 then 1 else (if x<1642 then 0 else 1))) else (if x<2618 then (if x<1714 then 0 else 1) else (if x<2646 then 1 else (if x<2680 then 2 else 0)))) else (if x<3186 then (if x<2786 then (if x<2764 then 2 else 0) else (if x<2800 then 1 else (if x<3102 then 2 else 2))) else (if x<3256 then (if x<3242 then 0 else 1) else (if x<3270 then 2 else (if x<3284 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3515 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2680,2710,2716,2730,2764,2786,2800,3102,3158,3178,3186,3192,3214,3242,3250,3256,3270,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3515 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3515 3158 5
  · have he : independentCachedBranchMembers3515.erase 3158=independentCachedBranchMembers3513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3513
  · have he : independentCachedBranchMembers3515.filter (independentCachedEdge 3158)=independentCachedBranchMembers3514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3514
def independentCachedBranchMembers3516 : Finset ℕ := ([250,1628,1642,1650,1714,1734,1768,2618,2638,2646,2680,2710,2764,2786,3102,3178,3186,3242,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound3516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3516 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3516 5 (fun x => (if x<2680 then (if x<1734 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1650 then 0 else (if x<1714 then 1 else 0))) else (if x<2618 then (if x<1768 then 1 else 1) else (if x<2638 then 0 else (if x<2646 then 2 else 1)))) else (if x<3178 then (if x<2764 then (if x<2710 then 1 else 2) else (if x<2786 then 1 else (if x<3102 then 0 else 2))) else (if x<3242 then (if x<3186 then 2 else 0) else (if x<3250 then 0 else (if x<3270 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3517 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2680,2710,2716,2730,2758,2764,2786,2800,3102,3158,3178,3186,3192,3214,3242,3250,3256,3270,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3517 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3517 2758 5
  · have he : independentCachedBranchMembers3517.erase 2758=independentCachedBranchMembers3515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3515
  · have he : independentCachedBranchMembers3517.filter (independentCachedEdge 2758)=independentCachedBranchMembers3516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3516
def independentCachedBranchMembers3518 : Finset ℕ := ([40,1628,1650,1720,1734,1748,1768,2618,2646,2680,2716,2764,2786,2800,3102,3186,3242,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3518 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3518 5 (fun x => (if x<2716 then (if x<1748 then (if x<1650 then (if x<1628 then 0 else 1) else (if x<1720 then 1 else (if x<1734 then 0 else 1))) else (if x<2618 then (if x<1768 then 0 else 1) else (if x<2646 then 0 else (if x<2680 then 0 else 1)))) else (if x<3186 then (if x<2786 then (if x<2764 then 2 else 1) else (if x<2800 then 1 else (if x<3102 then 2 else 2))) else (if x<3256 then (if x<3242 then 2 else 0) else (if x<3270 then 2 else (if x<3284 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3519 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2674,2680,2710,2716,2730,2758,2764,2786,2800,3102,3158,3178,3186,3192,3214,3242,3250,3256,3270,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3519 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3519 2674 5
  · have he : independentCachedBranchMembers3519.erase 2674=independentCachedBranchMembers3517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3517
  · have he : independentCachedBranchMembers3519.filter (independentCachedEdge 2674)=independentCachedBranchMembers3518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3518
def independentCachedBranchMembers3520 : Finset ℕ := ([1594,1628,1678,1768,2618,2638,2646,2710,2716,2786,2800,3102,3178,3186,3192,3242,3250,3256,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3520 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3520 5 (fun x => (if x<2800 then (if x<2638 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1768 then 0 else (if x<2618 then 0 else 1))) else (if x<2710 then (if x<2646 then 1 else 2) else (if x<2716 then 1 else (if x<2786 then 2 else 1)))) else (if x<3242 then (if x<3178 then (if x<3102 then 2 else 0) else (if x<3186 then 1 else (if x<3192 then 2 else 0))) else (if x<3270 then (if x<3250 then 0 else (if x<3256 then 1 else 2)) else (if x<3276 then 1 else (if x<3284 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3521 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2674,2680,2710,2716,2730,2758,2764,2786,2800,3102,3130,3158,3178,3186,3192,3214,3242,3250,3256,3270,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3521 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3521 3130 5
  · have he : independentCachedBranchMembers3521.erase 3130=independentCachedBranchMembers3519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3519
  · have he : independentCachedBranchMembers3521.filter (independentCachedEdge 3130)=independentCachedBranchMembers3520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3520
def independentCachedBranchMembers3522 : Finset ℕ := ([40,132,1594,1628,1642,1734,2618,2646,2710,2716,2730,2758,2764,2800,3102,3186,3192,3214,3250,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3522 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3522 5 (fun x => (if x<2758 then (if x<1734 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1628 then 0 else (if x<1642 then 1 else 1))) else (if x<2710 then (if x<2618 then 1 else (if x<2646 then 2 else 2)) else (if x<2716 then 3 else (if x<2730 then 2 else 3)))) else (if x<3192 then (if x<2800 then (if x<2764 then 0 else 3) else (if x<3102 then 2 else (if x<3186 then 2 else 2))) else (if x<3256 then (if x<3214 then 0 else (if x<3250 then 3 else 3)) else (if x<3284 then 2 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3523 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2674,2680,2710,2716,2730,2758,2764,2786,2800,3102,3130,3158,3178,3186,3192,3214,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3523 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3523 3312 5
  · have he : independentCachedBranchMembers3523.erase 3312=independentCachedBranchMembers3521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3521
  · have he : independentCachedBranchMembers3523.filter (independentCachedEdge 3312)=independentCachedBranchMembers3522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3522
def independentCachedBranchMembers3524 : Finset ℕ := ([48,250,1594,1628,1650,1720,2618,2638,2674,2710,2730,2764,2786,2800,3102,3158,3178,3192,3214,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3524 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3524 5 (fun x => (if x<2764 then (if x<1720 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1628 then 0 else (if x<1650 then 1 else 1))) else (if x<2674 then (if x<2618 then 1 else (if x<2638 then 2 else 2)) else (if x<2710 then 0 else (if x<2730 then 2 else 3)))) else (if x<3178 then (if x<2800 then (if x<2786 then 3 else 2) else (if x<3102 then 3 else (if x<3158 then 2 else 1))) else (if x<3250 then (if x<3192 then 2 else (if x<3214 then 0 else 3)) else (if x<3270 then 0 else (if x<3284 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3525 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2674,2680,2710,2716,2730,2758,2764,2786,2800,3102,3130,3158,3178,3186,3192,3214,3222,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3525 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3525 3222 5
  · have he : independentCachedBranchMembers3525.erase 3222=independentCachedBranchMembers3523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3523
  · have he : independentCachedBranchMembers3525.filter (independentCachedEdge 3222)=independentCachedBranchMembers3524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3524
def independentCachedBranchMembers3526 : Finset ℕ := ([48,132,1594,1628,1650,1678,1714,1734,1748,1768,2646,2680,2710,2730,2764,2786,2800,3130,3186,3214,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3526 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3526 5 (fun x => (if x<2680 then (if x<1678 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1628 then 0 else (if x<1650 then 1 else 1))) else (if x<1748 then (if x<1714 then 0 else (if x<1734 then 2 else 1)) else (if x<1768 then 2 else (if x<2646 then 1 else 1)))) else (if x<3130 then (if x<2764 then (if x<2710 then 0 else (if x<2730 then 2 else 2)) else (if x<2786 then 0 else (if x<2800 then 1 else 2))) else (if x<3250 then (if x<3186 then 3 else (if x<3214 then 0 else 3)) else (if x<3270 then 4 else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3527 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2674,2680,2710,2716,2730,2758,2764,2786,2792,2800,3102,3130,3158,3178,3186,3192,3214,3222,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3527 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3527 2792 5
  · have he : independentCachedBranchMembers3527.erase 2792=independentCachedBranchMembers3525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3525
  · have he : independentCachedBranchMembers3527.filter (independentCachedEdge 2792)=independentCachedBranchMembers3526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3526
def independentCachedBranchMembers3528 : Finset ℕ := ([48,250,1650,1678,1714,1720,1748,1768,2618,2646,2710,2716,2730,2758,2764,2800,3102,3186,3192,3214,3250,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3528 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3528 5 (fun x => (if x<2730 then (if x<1748 then (if x<1678 then (if x<250 then 0 else (if x<1650 then 0 else 0)) else (if x<1714 then 1 else (if x<1720 then 1 else 0))) else (if x<2646 then (if x<1768 then 1 else (if x<2618 then 1 else 0)) else (if x<2710 then 2 else (if x<2716 then 1 else 2)))) else (if x<3192 then (if x<2800 then (if x<2758 then 1 else (if x<2764 then 3 else 1)) else (if x<3102 then 0 else (if x<3186 then 2 else 2))) else (if x<3256 then (if x<3214 then 0 else (if x<3250 then 3 else 0)) else (if x<3284 then 2 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3529 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2674,2680,2710,2716,2730,2758,2764,2772,2786,2792,2800,3102,3130,3158,3178,3186,3192,3214,3222,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3529 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3529 2772 5
  · have he : independentCachedBranchMembers3529.erase 2772=independentCachedBranchMembers3527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3527
  · have he : independentCachedBranchMembers3529.filter (independentCachedEdge 2772)=independentCachedBranchMembers3528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3528
def independentCachedBranchMembers3530 : Finset ℕ := ([40,132,1642,1678,1714,1734,1748,1768,2618,2638,2674,2710,2730,2764,2786,2800,3102,3158,3178,3192,3214,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3530 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3530 5 (fun x => (if x<2730 then (if x<1748 then (if x<1678 then (if x<132 then 0 else (if x<1642 then 0 else 0)) else (if x<1714 then 1 else (if x<1734 then 1 else 0))) else (if x<2638 then (if x<1768 then 1 else (if x<2618 then 1 else 0)) else (if x<2674 then 2 else (if x<2710 then 2 else 0)))) else (if x<3178 then (if x<2800 then (if x<2764 then 1 else (if x<2786 then 1 else 3)) else (if x<3102 then 1 else (if x<3158 then 3 else 2))) else (if x<3250 then (if x<3192 then 2 else (if x<3214 then 0 else 2)) else (if x<3270 then 2 else (if x<3284 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3531 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,2618,2638,2646,2674,2680,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3158,3178,3186,3192,3214,3222,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3531 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3531 2738 5
  · have he : independentCachedBranchMembers3531.erase 2738=independentCachedBranchMembers3529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3529
  · have he : independentCachedBranchMembers3531.filter (independentCachedEdge 2738)=independentCachedBranchMembers3530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3530
def independentCachedBranchMembers3532 : Finset ℕ := ([40,132,1650,1678,1714,1720,1748,1768,2618,2646,2710,2716,2730,2758,2764,2800,3130,3158,3178,3222,3242,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3532 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3532 5 (fun x => (if x<2730 then (if x<1748 then (if x<1678 then (if x<132 then 0 else (if x<1650 then 0 else 1)) else (if x<1714 then 2 else (if x<1720 then 2 else 1))) else (if x<2646 then (if x<1768 then 0 else (if x<2618 then 2 else 0)) else (if x<2710 then 1 else (if x<2716 then 0 else 1)))) else (if x<3178 then (if x<2800 then (if x<2758 then 2 else (if x<2764 then 3 else 2)) else (if x<3130 then 1 else (if x<3158 then 3 else 3))) else (if x<3270 then (if x<3222 then 0 else (if x<3242 then 4 else 4)) else (if x<3276 then 0 else (if x<3312 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3533 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1714,1720,1734,1748,1768,1776,2618,2638,2646,2674,2680,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3158,3178,3186,3192,3214,3222,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3533 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3533 1776 5
  · have he : independentCachedBranchMembers3533.erase 1776=independentCachedBranchMembers3531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3531
  · have he : independentCachedBranchMembers3533.filter (independentCachedEdge 1776)=independentCachedBranchMembers3532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3532
def independentCachedBranchMembers3534 : Finset ℕ := ([48,250,1642,1678,1714,1734,1748,1768,2618,2638,2710,2730,2764,2786,2800,3186,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3534 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3534 5 (fun x => (if x<2730 then (if x<1734 then (if x<1642 then (if x<250 then 0 else 0) else (if x<1678 then 1 else (if x<1714 then 1 else 0))) else (if x<2618 then (if x<1748 then 2 else (if x<1768 then 3 else 2)) else (if x<2638 then 0 else (if x<2710 then 1 else 1)))) else (if x<3222 then (if x<2786 then (if x<2764 then 1 else 2) else (if x<2800 then 2 else (if x<3186 then 0 else 0))) else (if x<3276 then (if x<3242 then 3 else (if x<3256 then 3 else 0)) else (if x<3298 then 3 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3535 : Finset ℕ := ([1678,1768,2618,2638,2710,2786,2800,3186,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3535 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3535 4 (fun x => (if x<2786 then (if x<2618 then (if x<1768 then 0 else 0) else (if x<2638 then 1 else (if x<2710 then 1 else 0))) else (if x<3242 then (if x<2800 then 1 else (if x<3186 then 0 else 2)) else (if x<3256 then 2 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3536 : Finset ℕ := ([48,250,1642,1678,1714,1734,1748,1768,2618,2638,2710,2730,2764,2786,2800,3130,3186,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3536 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3536 3130 4
  · have he : independentCachedBranchMembers3536.erase 3130=independentCachedBranchMembers3534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3534
  · have he : independentCachedBranchMembers3536.filter (independentCachedEdge 3130)=independentCachedBranchMembers3535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3535
def independentCachedBranchMembers3537 : Finset ℕ := ([1734,1748,1768,2618,2764,2786,2800,3186,3222,3242,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3537 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3537 4 (fun x => (if x<2786 then (if x<1768 then (if x<1748 then 0 else 1) else (if x<2618 then 0 else (if x<2764 then 1 else 0))) else (if x<3222 then (if x<2800 then 0 else (if x<3186 then 1 else 2)) else (if x<3242 then 2 else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3538 : Finset ℕ := ([48,250,1642,1678,1714,1734,1748,1768,2618,2638,2674,2710,2730,2764,2786,2800,3130,3186,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3538 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3538 2674 4
  · have he : independentCachedBranchMembers3538.erase 2674=independentCachedBranchMembers3536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3536
  · have he : independentCachedBranchMembers3538.filter (independentCachedEdge 2674)=independentCachedBranchMembers3537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3537
def independentCachedBranchMembers3539 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1748,1768,1776,2618,2638,2646,2674,2680,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3158,3178,3186,3192,3214,3222,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3539 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3539 1686 5
  · have he : independentCachedBranchMembers3539.erase 1686=independentCachedBranchMembers3533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3533
  · have he : independentCachedBranchMembers3539.filter (independentCachedEdge 1686)=independentCachedBranchMembers3538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3538
def independentCachedBranchMembers3540 : Finset ℕ := ([40,48,250,1594,1734,1768,1776,2618,2638,2646,2680,2716,2730,2738,2758,2792,2800,3102,3178,3186,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3540 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3540 5 (fun x => (if x<2738 then (if x<1776 then (if x<1594 then (if x<48 then 0 else (if x<250 then 1 else 0)) else (if x<1734 then 0 else (if x<1768 then 1 else 0))) else (if x<2646 then (if x<2618 then 1 else (if x<2638 then 2 else 1)) else (if x<2716 then (if x<2680 then 2 else 0) else (if x<2730 then 2 else 0)))) else (if x<3186 then (if x<2800 then (if x<2758 then 3 else (if x<2792 then 3 else 3)) else (if x<3102 then 2 else (if x<3178 then 2 else 0))) else (if x<3256 then (if x<3214 then 2 else (if x<3222 then 1 else 3)) else (if x<3284 then (if x<3276 then 0 else 3) else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3541 : Finset ℕ := ([40,1594,1776,2646,2680,2716,2738,2758,2792,3102,3178,3214,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3541 4 (fun x => (if x<2738 then (if x<2646 then (if x<1594 then 0 else (if x<1776 then 0 else 1)) else (if x<2680 then 2 else (if x<2716 then 0 else 2))) else (if x<3102 then (if x<2758 then 1 else (if x<2792 then 3 else 1)) else (if x<3214 then (if x<3178 then 2 else 0) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3542 : Finset ℕ := ([40,48,250,1594,1714,1734,1768,1776,2618,2638,2646,2680,2716,2730,2738,2758,2792,2800,3102,3178,3186,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3542 1714 4
  · have he : independentCachedBranchMembers3542.erase 1714=independentCachedBranchMembers3540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3540
  · have he : independentCachedBranchMembers3542.filter (independentCachedEdge 1714)=independentCachedBranchMembers3541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3541
def independentCachedBranchMembers3543 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1748,1768,1776,2618,2638,2646,2674,2680,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3543 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3543 3228 5
  · have he : independentCachedBranchMembers3543.erase 3228=independentCachedBranchMembers3539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3539
  · have he : independentCachedBranchMembers3543.filter (independentCachedEdge 3228)=independentCachedBranchMembers3542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3542
def independentCachedBranchMembers3544 : Finset ℕ := ([40,132,250,1594,1650,1686,1748,1768,2618,2638,2674,2680,2710,2716,2730,2772,2786,2792,3102,3158,3178,3214,3250,3256,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3544 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3544 5 (fun x => (if x<2716 then (if x<1748 then (if x<1594 then (if x<132 then 0 else (if x<250 then 0 else 1)) else (if x<1650 then 0 else (if x<1686 then 1 else 0))) else (if x<2638 then (if x<1768 then 2 else (if x<2618 then 1 else 2)) else (if x<2680 then (if x<2674 then 3 else 3) else (if x<2710 then 0 else 2)))) else (if x<3178 then (if x<2786 then (if x<2730 then 4 else (if x<2772 then 3 else 0)) else (if x<3102 then (if x<2792 then 1 else 4) else (if x<3158 then 4 else 3))) else (if x<3256 then (if x<3214 then 0 else (if x<3250 then 3 else 3)) else (if x<3276 then (if x<3270 then 4 else 0) else (if x<3312 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3545 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1748,1768,1776,2618,2638,2646,2674,2680,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3545 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3545 3150 5
  · have he : independentCachedBranchMembers3545.erase 3150=independentCachedBranchMembers3543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3543
  · have he : independentCachedBranchMembers3545.filter (independentCachedEdge 3150)=independentCachedBranchMembers3544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3544
def independentCachedBranchMembers3546 : Finset ℕ := ([40,250,1594,1628,1642,1678,1714,1720,1748,1768,2638,2674,2680,2710,2716,2730,2758,2764,2800,3130,3158,3178,3214,3250,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3546 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3546 5 (fun x => (if x<2710 then (if x<1714 then (if x<1628 then (if x<250 then 0 else (if x<1594 then 0 else 0)) else (if x<1642 then 1 else (if x<1678 then 1 else 1))) else (if x<1768 then (if x<1720 then 2 else (if x<1748 then 1 else 2)) else (if x<2674 then (if x<2638 then 0 else 1) else (if x<2680 then 3 else 0)))) else (if x<3158 then (if x<2758 then (if x<2716 then 2 else (if x<2730 then 1 else 0)) else (if x<2800 then (if x<2764 then 3 else 2) else (if x<3130 then 2 else 3))) else (if x<3250 then (if x<3178 then 3 else (if x<3214 then 0 else 3)) else (if x<3284 then (if x<3256 then 4 else 0) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3547 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1748,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3547 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3547 2702 5
  · have he : independentCachedBranchMembers3547.erase 2702=independentCachedBranchMembers3545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3545
  · have he : independentCachedBranchMembers3547.filter (independentCachedEdge 2702)=independentCachedBranchMembers3546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3546
def independentCachedBranchMembers3548 : Finset ℕ := ([40,250,1594,1628,1650,1678,1714,1734,1748,1768,2646,2680,2710,2730,2764,2786,2800,3158,3178,3192,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3548 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3548 5 (fun x => (if x<2730 then (if x<1714 then (if x<1628 then (if x<250 then 0 else (if x<1594 then 0 else 0)) else (if x<1650 then 1 else (if x<1678 then 1 else 2))) else (if x<1768 then (if x<1734 then 2 else (if x<1748 then 1 else 2)) else (if x<2680 then (if x<2646 then 0 else 1) else (if x<2710 then 0 else 2)))) else (if x<3192 then (if x<2800 then (if x<2764 then 0 else (if x<2786 then 1 else 1)) else (if x<3158 then 2 else (if x<3178 then 3 else 0))) else (if x<3256 then (if x<3222 then 3 else (if x<3242 then 4 else 4)) else (if x<3298 then (if x<3276 then 0 else 3) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3549 : Finset ℕ := ([40,250,1650,1714,1734,1748,2680,2730,2764,3158,3222,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3549 4 (fun x => (if x<2680 then (if x<1714 then (if x<250 then 0 else (if x<1650 then 0 else 1)) else (if x<1734 then 2 else (if x<1748 then 1 else 2))) else (if x<3158 then (if x<2730 then 0 else (if x<2764 then 0 else 1)) else (if x<3298 then (if x<3222 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3550 : Finset ℕ := ([40,250,1594,1628,1650,1678,1714,1734,1748,1768,2646,2680,2710,2730,2764,2786,2800,3102,3158,3178,3192,3222,3242,3256,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3550 3102 4
  · have he : independentCachedBranchMembers3550.erase 3102=independentCachedBranchMembers3548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3548
  · have he : independentCachedBranchMembers3550.filter (independentCachedEdge 3102)=independentCachedBranchMembers3549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3549
def independentCachedBranchMembers3551 : Finset ℕ := ([40,48,132,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1740,1748,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3551 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3551 1740 5
  · have he : independentCachedBranchMembers3551.erase 1740=independentCachedBranchMembers3547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3547
  · have he : independentCachedBranchMembers3551.filter (independentCachedEdge 1740)=independentCachedBranchMembers3550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3550
def independentCachedBranchMembers3552 : Finset ℕ := ([40,48,250,1594,1642,1650,1714,1720,1768,1776,2618,2674,2680,2730,2738,2792,2800,3130,3178,3192,3242,3250,3256,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3552 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3552 5 (fun x => (if x<2680 then (if x<1714 then (if x<1594 then (if x<48 then 0 else (if x<250 then 1 else 0)) else (if x<1642 then 0 else (if x<1650 then 2 else 1))) else (if x<1776 then (if x<1720 then 2 else (if x<1768 then 1 else 0)) else (if x<2618 then 3 else (if x<2674 then 1 else 2)))) else (if x<3178 then (if x<2792 then (if x<2730 then 0 else (if x<2738 then 0 else 3)) else (if x<2800 then 3 else (if x<3130 then 1 else 2))) else (if x<3250 then (if x<3192 then 0 else (if x<3242 then 1 else 4)) else (if x<3298 then (if x<3256 then 1 else 0) else (if x<3312 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3553 : Finset ℕ := ([40,1650,1720,1768,2674,2730,2792,3130,3178,3192,3250,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3553 4 (fun x => (if x<2792 then (if x<1768 then (if x<1650 then 0 else (if x<1720 then 1 else 0)) else (if x<2674 then 1 else (if x<2730 then 2 else 0))) else (if x<3192 then (if x<3130 then 2 else (if x<3178 then 0 else 1)) else (if x<3298 then (if x<3250 then 2 else 3) else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3554 : Finset ℕ := ([40,48,250,1594,1642,1650,1714,1720,1768,1776,2618,2674,2680,2730,2738,2792,2800,3130,3178,3186,3192,3242,3250,3256,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3554 3186 4
  · have he : independentCachedBranchMembers3554.erase 3186=independentCachedBranchMembers3552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3552
  · have he : independentCachedBranchMembers3554.filter (independentCachedEdge 3186)=independentCachedBranchMembers3553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3553
def independentCachedBranchMembers3555 : Finset ℕ := ([40,48,1594,1720,2674,2730,2738,2792,2800,3130,3192,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3555 4 (fun x => (if x<2738 then (if x<1720 then (if x<48 then 0 else (if x<1594 then 1 else 0)) else (if x<2674 then 1 else (if x<2730 then 2 else 0))) else (if x<3130 then (if x<2792 then 1 else (if x<2800 then 2 else 3)) else (if x<3256 then (if x<3192 then 1 else 2) else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3556 : Finset ℕ := ([40,48,250,1594,1642,1650,1714,1720,1768,1776,2618,2674,2680,2730,2738,2786,2792,2800,3130,3178,3186,3192,3242,3250,3256,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3556 2786 4
  · have he : independentCachedBranchMembers3556.erase 2786=independentCachedBranchMembers3554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3554
  · have he : independentCachedBranchMembers3556.filter (independentCachedEdge 2786)=independentCachedBranchMembers3555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3555
def independentCachedBranchMembers3557 : Finset ℕ := ([40,48,132,222,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1740,1748,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3557 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3557 222 5
  · have he : independentCachedBranchMembers3557.erase 222=independentCachedBranchMembers3551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3551
  · have he : independentCachedBranchMembers3557.filter (independentCachedEdge 222)=independentCachedBranchMembers3556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3556
def independentCachedBranchMembers3558 : Finset ℕ := ([40,132,250,1594,1642,1720,1734,1748,1768,2618,2680,2710,2730,2758,2772,2792,3130,3158,3178,3192,3222,3242,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3558 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3558 5 (fun x => (if x<2710 then (if x<1720 then (if x<250 then (if x<132 then 0 else 0) else (if x<1594 then 1 else (if x<1642 then 0 else 1))) else (if x<1768 then (if x<1734 then 1 else (if x<1748 then 2 else 3)) else (if x<2618 then 2 else (if x<2680 then 1 else 0)))) else (if x<3158 then (if x<2772 then (if x<2730 then 2 else (if x<2758 then 3 else 3)) else (if x<2792 then 0 else (if x<3130 then 1 else 3))) else (if x<3222 then (if x<3178 then 2 else (if x<3192 then 0 else 1)) else (if x<3242 then 4 else (if x<3256 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3559 : Finset ℕ := ([250,1720,1748,1768,2680,2772,2792,3130,3158,3178,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound3559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3559 4 (fun x => (if x<2792 then (if x<1768 then (if x<1720 then 0 else (if x<1748 then 0 else 1)) else (if x<2680 then 1 else (if x<2772 then 0 else 2))) else (if x<3178 then (if x<3130 then 2 else (if x<3158 then 0 else 1)) else (if x<3222 then 1 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3560 : Finset ℕ := ([40,132,250,1594,1642,1720,1734,1748,1768,2618,2680,2710,2730,2758,2772,2792,3130,3158,3178,3192,3222,3242,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3560 3284 4
  · have he : independentCachedBranchMembers3560.erase 3284=independentCachedBranchMembers3558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3558
  · have he : independentCachedBranchMembers3560.filter (independentCachedEdge 3284)=independentCachedBranchMembers3559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3559
def independentCachedBranchMembers3561 : Finset ℕ := ([250,1642,1734,1748,1768,2618,2710,2730,3130,3222,3242,3256] : List ℕ).toFinset
theorem independentCachedBranchBound3561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3561 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3561 4 (fun x => (if x<2710 then (if x<1748 then (if x<1642 then 0 else (if x<1734 then 0 else 1)) else (if x<1768 then 2 else (if x<2618 then 1 else 0))) else (if x<3222 then (if x<2730 then 1 else (if x<3130 then 2 else 2)) else (if x<3242 then 3 else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3562 : Finset ℕ := ([40,132,250,1594,1642,1686,1720,1734,1748,1768,2618,2680,2710,2730,2758,2772,2792,3130,3158,3178,3192,3222,3242,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3562 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3562 1686 4
  · have he : independentCachedBranchMembers3562.erase 1686=independentCachedBranchMembers3560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3560
  · have he : independentCachedBranchMembers3562.filter (independentCachedEdge 1686)=independentCachedBranchMembers3561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3561
def independentCachedBranchMembers3563 : Finset ℕ := ([250,1642,1734,1768,2730,2758,2792,3130,3158,3192,3222,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3563 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3563 4 (fun x => (if x<2792 then (if x<1768 then (if x<1642 then 0 else (if x<1734 then 0 else 1)) else (if x<2730 then 1 else (if x<2758 then 0 else 2))) else (if x<3192 then (if x<3130 then 2 else (if x<3158 then 0 else 1)) else (if x<3256 then (if x<3222 then 1 else 2) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3564 : Finset ℕ := ([40,132,250,1594,1642,1686,1720,1734,1748,1768,2618,2680,2710,2730,2758,2772,2792,3130,3158,3178,3192,3222,3242,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3564 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3564 3270 4
  · have he : independentCachedBranchMembers3564.erase 3270=independentCachedBranchMembers3562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3562
  · have he : independentCachedBranchMembers3564.filter (independentCachedEdge 3270)=independentCachedBranchMembers3563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3563
def independentCachedBranchMembers3565 : Finset ℕ := ([132,250,1594,1642,2710,2730,2758,2772,2792,3130,3158,3178,3192] : List ℕ).toFinset
theorem independentCachedBranchBound3565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3565 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3565 4 (fun x => (if x<2758 then (if x<1642 then (if x<250 then 0 else (if x<1594 then 1 else 0)) else (if x<2710 then 1 else (if x<2730 then 2 else 1))) else (if x<3130 then (if x<2772 then 0 else (if x<2792 then 3 else 3)) else (if x<3178 then (if x<3158 then 1 else 2) else (if x<3192 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3566 : Finset ℕ := ([40,132,250,1594,1642,1686,1720,1734,1748,1768,2618,2646,2680,2710,2730,2758,2772,2792,3130,3158,3178,3192,3222,3242,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3566 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3566 2646 4
  · have he : independentCachedBranchMembers3566.erase 2646=independentCachedBranchMembers3564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3564
  · have he : independentCachedBranchMembers3566.filter (independentCachedEdge 2646)=independentCachedBranchMembers3565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3565
def independentCachedBranchMembers3567 : Finset ℕ := ([12,40,48,132,222,250,1594,1628,1642,1650,1678,1686,1714,1720,1734,1740,1748,1768,1776,2618,2638,2646,2674,2680,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3178,3186,3192,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound3567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3567 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3567 12 5
  · have he : independentCachedBranchMembers3567.erase 12=independentCachedBranchMembers3557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3557
  · have he : independentCachedBranchMembers3567.filter (independentCachedEdge 12)=independentCachedBranchMembers3566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3566
def independentCachedBranchMembers3568 : Finset ℕ := ([48,132,1628,1642,1650,1714,1734,1768,1776,2618,2638,2680,2710,2764,2786,3130,3158,3192,3214,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3568 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3568 5 (fun x => (if x<2680 then (if x<1714 then (if x<1628 then (if x<132 then 0 else 0) else (if x<1642 then 1 else (if x<1650 then 1 else 0))) else (if x<1776 then (if x<1734 then 2 else (if x<1768 then 0 else 2)) else (if x<2618 then 1 else (if x<2638 then 0 else 1)))) else (if x<3192 then (if x<2786 then (if x<2710 then 1 else (if x<2764 then 2 else 2)) else (if x<3130 then 1 else (if x<3158 then 3 else 3))) else (if x<3276 then (if x<3214 then 0 else (if x<3256 then 3 else 4)) else (if x<3284 then 0 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3569 : Finset ℕ := ([48,1628,1650,1714,1776,2638,2764,2786,3214,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3569 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3569 4 (fun x => (if x<2638 then (if x<1650 then (if x<1628 then 0 else 1) else (if x<1714 then 0 else (if x<1776 then 2 else 1))) else (if x<3214 then (if x<2764 then 1 else (if x<2786 then 0 else 1)) else (if x<3276 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3570 : Finset ℕ := ([40,48,132,1628,1642,1650,1714,1734,1768,1776,2618,2638,2680,2710,2764,2786,3130,3158,3192,3214,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3570 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3570 40 4
  · have he : independentCachedBranchMembers3570.erase 40=independentCachedBranchMembers3568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3568
  · have he : independentCachedBranchMembers3570.filter (independentCachedEdge 40)=independentCachedBranchMembers3569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3569
def independentCachedBranchMembers3571 : Finset ℕ := ([48,1650,1714,1768,2618,2710,2764,3192,3214,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3571 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3571 4 (fun x => (if x<2764 then (if x<1768 then (if x<1650 then 0 else (if x<1714 then 0 else 1)) else (if x<2618 then 1 else (if x<2710 then 0 else 1))) else (if x<3256 then (if x<3192 then 1 else (if x<3214 then 0 else 2)) else (if x<3284 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3572 : Finset ℕ := ([40,48,132,1628,1642,1650,1714,1734,1768,1776,2618,2638,2680,2710,2764,2772,2786,3130,3158,3192,3214,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3572 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3572 2772 4
  · have he : independentCachedBranchMembers3572.erase 2772=independentCachedBranchMembers3570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3570
  · have he : independentCachedBranchMembers3572.filter (independentCachedEdge 2772)=independentCachedBranchMembers3571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3571
def independentCachedBranchMembers3573 : Finset ℕ := ([48,1628,1650,1776,2618,2638,2710,2764,2786,3158,3192,3214,3284] : List ℕ).toFinset
theorem independentCachedBranchBound3573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3573 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3573 4 (fun x => (if x<2710 then (if x<1776 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<2618 then 1 else (if x<2638 then 0 else 1))) else (if x<3158 then (if x<2764 then 2 else (if x<2786 then 2 else 1)) else (if x<3214 then (if x<3192 then 3 else 0) else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3574 : Finset ℕ := ([40,48,132,1628,1642,1650,1714,1734,1768,1776,2618,2638,2680,2710,2764,2772,2786,3130,3158,3192,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3574 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3574 3222 4
  · have he : independentCachedBranchMembers3574.erase 3222=independentCachedBranchMembers3572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3572
  · have he : independentCachedBranchMembers3574.filter (independentCachedEdge 3222)=independentCachedBranchMembers3573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3573
def independentCachedBranchMembers3575 : Finset ℕ := ([40,132,1650,1768,2618,2638,2680,2710,2772,2786,3158,3214,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3575 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3575 4 (fun x => (if x<2710 then (if x<1768 then (if x<132 then 0 else (if x<1650 then 0 else 1)) else (if x<2638 then (if x<2618 then 1 else 0) else (if x<2680 then 2 else 1))) else (if x<3158 then (if x<2772 then 0 else (if x<2786 then 2 else 1)) else (if x<3256 then (if x<3214 then 2 else 3) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3576 : Finset ℕ := ([40,48,132,1628,1642,1650,1714,1734,1768,1776,2618,2638,2680,2710,2764,2772,2786,3130,3150,3158,3192,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3576 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3576 3150 4
  · have he : independentCachedBranchMembers3576.erase 3150=independentCachedBranchMembers3574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3574
  · have he : independentCachedBranchMembers3576.filter (independentCachedEdge 3150)=independentCachedBranchMembers3575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3575
def independentCachedBranchMembers3577 : Finset ℕ := ([48,132,1642,1714,1776,2638,2710,2772,3130,3158,3192,3214,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3577 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3577 4 (fun x => (if x<2772 then (if x<1714 then (if x<132 then 0 else (if x<1642 then 0 else 1)) else (if x<2638 then (if x<1776 then 1 else 2) else (if x<2710 then 1 else 1))) else (if x<3192 then (if x<3130 then 2 else (if x<3158 then 0 else 3)) else (if x<3276 then (if x<3214 then 3 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3578 : Finset ℕ := ([40,48,132,1628,1642,1650,1714,1734,1768,1776,2618,2638,2646,2680,2710,2764,2772,2786,3130,3150,3158,3192,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3578 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3578 2646 4
  · have he : independentCachedBranchMembers3578.erase 2646=independentCachedBranchMembers3576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3576
  · have he : independentCachedBranchMembers3578.filter (independentCachedEdge 2646)=independentCachedBranchMembers3577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3577
def independentCachedBranchMembers3579 : Finset ℕ := ([40,48,1642,1650,1714,1768,1776,2618,2680,2786,3130,3192,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3579 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3579 4 (fun x => (if x<2618 then (if x<1650 then (if x<48 then 0 else (if x<1642 then 1 else 0)) else (if x<1768 then (if x<1714 then 1 else 2) else (if x<1776 then 2 else 3))) else (if x<3130 then (if x<2680 then 0 else (if x<2786 then 1 else 2)) else (if x<3256 then (if x<3192 then 1 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3580 : Finset ℕ := ([40,48,132,222,1628,1642,1650,1714,1734,1768,1776,2618,2638,2646,2680,2710,2764,2772,2786,3130,3150,3158,3192,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3580 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3580 222 4
  · have he : independentCachedBranchMembers3580.erase 222=independentCachedBranchMembers3578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3578
  · have he : independentCachedBranchMembers3580.filter (independentCachedEdge 222)=independentCachedBranchMembers3579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3579
def independentCachedBranchMembers3581 : Finset ℕ := ([1628,1642,1714,1768,2638,2680,2710,2764,3130,3158,3214,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3581 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3581 4 (fun x => (if x<2764 then (if x<1768 then (if x<1642 then 0 else (if x<1714 then 0 else 1)) else (if x<2680 then (if x<2638 then 1 else 0) else (if x<2710 then 0 else 1))) else (if x<3214 then (if x<3130 then 1 else (if x<3158 then 2 else 2)) else (if x<3284 then (if x<3256 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3582 : Finset ℕ := ([1628,1714,2638,2764,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3582 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3582 3 (fun x => (if x<2764 then (if x<1714 then 0 else (if x<2638 then 1 else 0)) else (if x<3214 then 1 else (if x<3298 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers3583 : Finset ℕ := ([40,1628,1642,1714,1768,2638,2680,2710,2764,3130,3158,3214,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound3583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3583 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers3583 40 3
  · have he : independentCachedBranchMembers3583.erase 40=independentCachedBranchMembers3581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3581
  · have he : independentCachedBranchMembers3583.filter (independentCachedEdge 40)=independentCachedBranchMembers3582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3582
end EntropyDesigns.QuadraticRefinement
