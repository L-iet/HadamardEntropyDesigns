/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch84
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5504 : Finset ℕ := ([1642,1644,1650,1652,1708,1714,1734,1752,2618,2620,2638,2646,2702,2710,2786,2788,3174,3192,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5504 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5504 5 (fun x => (if x<2646 then (if x<1714 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else (if x<1708 then 0 else 0))) else (if x<2618 then (if x<1734 then 0 else (if x<1752 then 0 else 0)) else (if x<2620 then 2 else (if x<2638 then 3 else 2)))) else (if x<3174 then (if x<2710 then (if x<2702 then 3 else 3) else (if x<2786 then 2 else (if x<2788 then 2 else 3))) else (if x<3276 then (if x<3192 then 1 else (if x<3274 then 1 else 4)) else (if x<3282 then 1 else (if x<3284 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5505 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3244,3250,3252,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5505 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5505 3288 5
  · have he : independentCachedBranchMembers5505.erase 3288=independentCachedBranchMembers5503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5503
  · have he : independentCachedBranchMembers5505.filter (independentCachedEdge 3288)=independentCachedBranchMembers5504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5504
def independentCachedBranchMembers5506 : Finset ℕ := ([1642,1644,1650,1652,1708,1714,1734,1752,2606,2614,2650,2652,2714,2716,2792,2800,3174,3192,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5506 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5506 5 (fun x => (if x<2652 then (if x<1714 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else (if x<1708 then 0 else 0))) else (if x<2606 then (if x<1734 then 0 else (if x<1752 then 0 else 0)) else (if x<2614 then 2 else (if x<2650 then 3 else 2)))) else (if x<3174 then (if x<2716 then (if x<2714 then 3 else 3) else (if x<2792 then 2 else (if x<2800 then 2 else 3))) else (if x<3276 then (if x<3192 then 1 else (if x<3274 then 1 else 4)) else (if x<3282 then 1 else (if x<3284 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5507 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3192,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5507 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5507 3270 5
  · have he : independentCachedBranchMembers5507.erase 3270=independentCachedBranchMembers5505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5505
  · have he : independentCachedBranchMembers5507.filter (independentCachedEdge 3270)=independentCachedBranchMembers5506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5506
def independentCachedBranchMembers5508 : Finset ℕ := ([1644,1650,1702,1720,1734,1738,1748,1752,2606,2620,2638,2652,2710,2714,2788,2792,3174,3192,3244,3250,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5508 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5508 5 (fun x => (if x<2652 then (if x<1738 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1734 then 0 else 1))) else (if x<2606 then (if x<1748 then 0 else (if x<1752 then 0 else 1)) else (if x<2620 then 2 else (if x<2638 then 3 else 3)))) else (if x<3174 then (if x<2714 then (if x<2710 then 2 else 2) else (if x<2788 then 3 else (if x<2792 then 2 else 3))) else (if x<3250 then (if x<3192 then 1 else (if x<3244 then 1 else 4)) else (if x<3276 then 4 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5509 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3186,3192,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5509 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5509 3186 5
  · have he : independentCachedBranchMembers5509.erase 3186=independentCachedBranchMembers5507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5507
  · have he : independentCachedBranchMembers5509.filter (independentCachedEdge 3186)=independentCachedBranchMembers5508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5508
def independentCachedBranchMembers5510 : Finset ℕ := ([1644,1650,1702,1720,1734,1738,1748,1752,2614,2618,2646,2650,2702,2716,2786,2800,3174,3192,3244,3250,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5510 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5510 5 (fun x => (if x<2650 then (if x<1738 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1734 then 0 else 1))) else (if x<2614 then (if x<1748 then 0 else (if x<1752 then 0 else 1)) else (if x<2618 then 2 else (if x<2646 then 3 else 3)))) else (if x<3174 then (if x<2716 then (if x<2702 then 2 else 2) else (if x<2786 then 3 else (if x<2800 then 2 else 3))) else (if x<3250 then (if x<3192 then 1 else (if x<3244 then 1 else 4)) else (if x<3276 then 4 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5511 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3180,3186,3192,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5511 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5511 3180 5
  · have he : independentCachedBranchMembers5511.erase 3180=independentCachedBranchMembers5509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5509
  · have he : independentCachedBranchMembers5511.filter (independentCachedEdge 3180)=independentCachedBranchMembers5510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5510
def independentCachedBranchMembers5512 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1738,1748,2606,2614,2650,2652,2702,2710,2786,2788,3174,3192,3242,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5512 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5512 5 (fun x => (if x<2702 then (if x<1738 then (if x<1652 then (if x<1644 then 0 else (if x<1650 then 1 else 1)) else (if x<1702 then 0 else (if x<1720 then 0 else 0))) else (if x<2614 then (if x<1748 then 1 else (if x<2606 then 1 else 2)) else (if x<2650 then 3 else (if x<2652 then 2 else 3)))) else (if x<3242 then (if x<2788 then (if x<2710 then 3 else (if x<2786 then 2 else 2)) else (if x<3174 then 3 else (if x<3192 then 0 else 0))) else (if x<3252 then (if x<3244 then 0 else (if x<3250 then 4 else 4)) else (if x<3270 then 0 else (if x<3288 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5513 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3180,3186,3192,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5513 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5513 3256 5
  · have he : independentCachedBranchMembers5513.erase 3256=independentCachedBranchMembers5511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5511
  · have he : independentCachedBranchMembers5513.filter (independentCachedEdge 3256)=independentCachedBranchMembers5512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5512
def independentCachedBranchMembers5514 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1738,1748,2618,2620,2638,2646,2714,2716,2792,2800,3174,3192,3242,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5514 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5514 5 (fun x => (if x<2714 then (if x<1738 then (if x<1652 then (if x<1644 then 0 else (if x<1650 then 1 else 1)) else (if x<1702 then 0 else (if x<1720 then 0 else 0))) else (if x<2620 then (if x<1748 then 1 else (if x<2618 then 1 else 2)) else (if x<2638 then 3 else (if x<2646 then 2 else 3)))) else (if x<3242 then (if x<2800 then (if x<2716 then 3 else (if x<2792 then 2 else 2)) else (if x<3174 then 3 else (if x<3192 then 0 else 0))) else (if x<3252 then (if x<3244 then 0 else (if x<3250 then 4 else 4)) else (if x<3270 then 0 else (if x<3288 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5515 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3180,3186,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5515 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5515 3238 5
  · have he : independentCachedBranchMembers5515.erase 3238=independentCachedBranchMembers5513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5513
  · have he : independentCachedBranchMembers5515.filter (independentCachedEdge 3238)=independentCachedBranchMembers5514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5514
def independentCachedBranchMembers5516 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1734,1752,2606,2618,2638,2650,2710,2716,2786,2792,3174,3180,3186,3192,3242,3252,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5516 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5516 5 (fun x => (if x<2710 then (if x<1734 then (if x<1708 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<1714 then 1 else (if x<1720 then 1 else 0))) else (if x<2618 then (if x<1752 then 1 else (if x<2606 then 1 else 2)) else (if x<2638 then 3 else (if x<2650 then 3 else 2)))) else (if x<3186 then (if x<2792 then (if x<2716 then 2 else (if x<2786 then 3 else 2)) else (if x<3174 then 3 else (if x<3180 then 0 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3242 then 0 else 0)) else (if x<3274 then 0 else (if x<3284 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5517 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5517 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5517 3188 5
  · have he : independentCachedBranchMembers5517.erase 3188=independentCachedBranchMembers5515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5515
  · have he : independentCachedBranchMembers5517.filter (independentCachedEdge 3188)=independentCachedBranchMembers5516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5516
def independentCachedBranchMembers5518 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1734,1752,2614,2620,2646,2652,2702,2714,2788,2800,3174,3180,3186,3192,3242,3252,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5518 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5518 5 (fun x => (if x<2702 then (if x<1734 then (if x<1708 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<1714 then 1 else (if x<1720 then 1 else 0))) else (if x<2620 then (if x<1752 then 1 else (if x<2614 then 1 else 2)) else (if x<2646 then 3 else (if x<2652 then 3 else 2)))) else (if x<3186 then (if x<2800 then (if x<2714 then 2 else (if x<2788 then 3 else 2)) else (if x<3174 then 3 else (if x<3180 then 0 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3242 then 0 else 0)) else (if x<3274 then 0 else (if x<3284 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5519 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5519 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5519 3178 5
  · have he : independentCachedBranchMembers5519.erase 3178=independentCachedBranchMembers5517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5517
  · have he : independentCachedBranchMembers5519.filter (independentCachedEdge 3178)=independentCachedBranchMembers5518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5518
def independentCachedBranchMembers5520 : Finset ℕ := ([1714,1738,2614,2618,2638,2646,2650,2702,2710,2714,2786,3102,3174,3178,3186,3238,3242,3250,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5520 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5520 5 (fun x => (if x<2786 then (if x<2646 then (if x<2614 then (if x<1738 then 0 else 0) else (if x<2618 then 0 else (if x<2638 then 1 else 0))) else (if x<2702 then (if x<2650 then 1 else 2) else (if x<2710 then 1 else (if x<2714 then 2 else 0)))) else (if x<3238 then (if x<3174 then (if x<3102 then 0 else 1) else (if x<3178 then 3 else (if x<3186 then 2 else 1))) else (if x<3270 then (if x<3242 then 2 else (if x<3250 then 1 else 3)) else (if x<3274 then 1 else (if x<3282 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5521 : Finset ℕ := ([1738,2614,2650,2714,3102,3178,3186,3242,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound5521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5521 4 (fun x => (if x<3178 then (if x<2650 then (if x<2614 then 0 else 0) else (if x<2714 then 0 else (if x<3102 then 1 else 1))) else (if x<3242 then (if x<3186 then 2 else 3) else (if x<3250 then 1 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5522 : Finset ℕ := ([1714,1734,1738,2614,2618,2638,2646,2650,2702,2710,2714,2786,3102,3174,3178,3186,3238,3242,3250,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5522 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5522 1734 4
  · have he : independentCachedBranchMembers5522.erase 1734=independentCachedBranchMembers5520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5520
  · have he : independentCachedBranchMembers5522.filter (independentCachedEdge 1734)=independentCachedBranchMembers5521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5521
def independentCachedBranchMembers5523 : Finset ℕ := ([1714,2638,2710,2714,3102,3186,3238,3242,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5523 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5523 4 (fun x => (if x<3186 then (if x<2710 then (if x<2638 then 0 else 0) else (if x<2714 then 0 else (if x<3102 then 1 else 1))) else (if x<3242 then (if x<3238 then 2 else 2) else (if x<3270 then 1 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5524 : Finset ℕ := ([1650,1714,1734,1738,2614,2618,2638,2646,2650,2702,2710,2714,2786,3102,3174,3178,3186,3238,3242,3250,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5524 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5524 1650 4
  · have he : independentCachedBranchMembers5524.erase 1650=independentCachedBranchMembers5522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5522
  · have he : independentCachedBranchMembers5524.filter (independentCachedEdge 1650)=independentCachedBranchMembers5523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5523
def independentCachedBranchMembers5525 : Finset ℕ := ([1650,1714,1734,1738,2614,2618,2638,2702,3186,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5525 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5525 4 (fun x => (if x<2638 then (if x<1738 then (if x<1714 then 0 else (if x<1734 then 1 else 0)) else (if x<2614 then 1 else (if x<2618 then 1 else 0))) else (if x<3250 then (if x<2702 then 1 else (if x<3186 then 0 else 2)) else (if x<3270 then 3 else (if x<3274 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5526 : Finset ℕ := ([1650,1714,1734,1738,2606,2614,2618,2638,2646,2650,2702,2710,2714,2786,3102,3174,3178,3186,3238,3242,3250,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5526 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5526 2606 4
  · have he : independentCachedBranchMembers5526.erase 2606=independentCachedBranchMembers5524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5524
  · have he : independentCachedBranchMembers5526.filter (independentCachedEdge 2606)=independentCachedBranchMembers5525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5525
def independentCachedBranchMembers5527 : Finset ℕ := ([1714,1734,2618,2638,2646,2714,3102,3178,3186,3238,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5527 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5527 4 (fun x => (if x<3102 then (if x<2638 then (if x<1734 then 0 else (if x<2618 then 0 else 0)) else (if x<2646 then 0 else (if x<2714 then 1 else 1))) else (if x<3238 then (if x<3178 then 1 else (if x<3186 then 2 else 3)) else (if x<3274 then 2 else (if x<3282 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5528 : Finset ℕ := ([1650,1702,1714,1734,1738,2606,2614,2618,2638,2646,2650,2702,2710,2714,2786,3102,3174,3178,3186,3238,3242,3250,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5528 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5528 1702 4
  · have he : independentCachedBranchMembers5528.erase 1702=independentCachedBranchMembers5526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5526
  · have he : independentCachedBranchMembers5528.filter (independentCachedEdge 1702)=independentCachedBranchMembers5527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5527
def independentCachedBranchMembers5529 : Finset ℕ := ([1650,1738,2614,2646,2702,2714,3102,3178,3238,3250,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5529 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5529 4 (fun x => (if x<3102 then (if x<2646 then (if x<1738 then 0 else (if x<2614 then 0 else 0)) else (if x<2702 then 1 else (if x<2714 then 0 else 1))) else (if x<3250 then (if x<3178 then 1 else (if x<3238 then 2 else 2)) else (if x<3270 then 3 else (if x<3282 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5530 : Finset ℕ := ([1642,1650,1702,1714,1734,1738,2606,2614,2618,2638,2646,2650,2702,2710,2714,2786,3102,3174,3178,3186,3238,3242,3250,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5530 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5530 1642 4
  · have he : independentCachedBranchMembers5530.erase 1642=independentCachedBranchMembers5528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5528
  · have he : independentCachedBranchMembers5530.filter (independentCachedEdge 1642)=independentCachedBranchMembers5529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5529
def independentCachedBranchMembers5531 : Finset ℕ := ([252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5531 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5531 252 5
  · have he : independentCachedBranchMembers5531.erase 252=independentCachedBranchMembers5519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5519
  · have he : independentCachedBranchMembers5531.filter (independentCachedEdge 252)=independentCachedBranchMembers5530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5530
def independentCachedBranchMembers5532 : Finset ℕ := ([1644,1652,1714,1720,1738,1752,2606,2614,2620,2638,2646,2652,2714,2786,2792,2800,3102,3174,3180,3188,3242,3250,3256,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5532 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5532 5 (fun x => (if x<2786 then (if x<2606 then (if x<1720 then (if x<1652 then 0 else (if x<1714 then 1 else 1)) else (if x<1738 then 0 else (if x<1752 then 0 else 1))) else (if x<2638 then (if x<2614 then 2 else (if x<2620 then 1 else 0)) else (if x<2652 then (if x<2646 then 0 else 2) else (if x<2714 then 1 else 0)))) else (if x<3188 then (if x<3102 then (if x<2792 then 2 else (if x<2800 then 0 else 1)) else (if x<3174 then 2 else (if x<3180 then 2 else 3))) else (if x<3256 then (if x<3242 then 4 else (if x<3250 then 2 else 4)) else (if x<3282 then (if x<3274 then 3 else 3) else (if x<3288 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5533 : Finset ℕ := ([132,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5533 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5533 132 5
  · have he : independentCachedBranchMembers5533.erase 132=independentCachedBranchMembers5531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5531
  · have he : independentCachedBranchMembers5533.filter (independentCachedEdge 132)=independentCachedBranchMembers5532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5532
def independentCachedBranchMembers5534 : Finset ℕ := ([1650,1652,1708,1720,1734,1748,2606,2618,2620,2646,2702,2714,2716,2786,2788,2800,3102,3174,3186,3188,3242,3244,3256,3270,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5534 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5534 5 (fun x => (if x<2786 then (if x<2606 then (if x<1720 then (if x<1652 then 0 else (if x<1708 then 1 else 1)) else (if x<1734 then 0 else (if x<1748 then 1 else 0))) else (if x<2646 then (if x<2618 then 2 else (if x<2620 then 0 else 1)) else (if x<2714 then (if x<2702 then 0 else 1) else (if x<2716 then 2 else 0)))) else (if x<3188 then (if x<3102 then (if x<2788 then 2 else (if x<2800 then 1 else 0)) else (if x<3174 then 2 else (if x<3186 then 2 else 3))) else (if x<3256 then (if x<3242 then 4 else (if x<3244 then 2 else 4)) else (if x<3282 then (if x<3270 then 3 else 4) else (if x<3284 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5535 : Finset ℕ := ([72,132,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5535 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5535 72 5
  · have he : independentCachedBranchMembers5535.erase 72=independentCachedBranchMembers5533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5533
  · have he : independentCachedBranchMembers5535.filter (independentCachedEdge 72)=independentCachedBranchMembers5534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5534
end EntropyDesigns.QuadraticRefinement
