/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch19
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2560 : Finset ℕ := ([222,1626,1652,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2714,2740,2764,2786,2800,3102,3188,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2560 1652 4
  · have he : independentCachedBranchMembers2560.erase 1652=independentCachedBranchMembers2558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2558
  · have he : independentCachedBranchMembers2560.filter (independentCachedEdge 1652)=independentCachedBranchMembers2559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2559
def independentCachedBranchMembers2561 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1652,1678,1692,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2674,2702,2714,2738,2740,2762,2764,2776,2786,2800,3102,3150,3164,3186,3188,3226,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2561 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2561 2738 5
  · have he : independentCachedBranchMembers2561.erase 2738=independentCachedBranchMembers2557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2557
  · have he : independentCachedBranchMembers2561.filter (independentCachedEdge 2738)=independentCachedBranchMembers2560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2560
def independentCachedBranchMembers2562 : Finset ℕ := ([12,48,72,222,1626,1628,1678,1714,1738,1740,1776,2614,2638,2674,2714,2776,2786,3102,3164,3250,3252,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2562 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2562 5 (fun x => (if x<2638 then (if x<1678 then (if x<222 then (if x<48 then 0 else (if x<72 then 0 else 1)) else (if x<1626 then 1 else (if x<1628 then 1 else 2))) else (if x<1740 then (if x<1714 then 0 else (if x<1738 then 0 else 2)) else (if x<1776 then 1 else (if x<2614 then 2 else 3)))) else (if x<3164 then (if x<2776 then (if x<2674 then 0 else (if x<2714 then 0 else 3)) else (if x<2786 then 1 else (if x<3102 then 2 else 3))) else (if x<3274 then (if x<3250 then 1 else (if x<3252 then 3 else 4)) else (if x<3276 then 1 else (if x<3312 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2563 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1652,1678,1692,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2738,2740,2762,2764,2776,2786,2800,3102,3150,3164,3186,3188,3226,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2563 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2563 2662 5
  · have he : independentCachedBranchMembers2563.erase 2662=independentCachedBranchMembers2561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2561
  · have he : independentCachedBranchMembers2563.filter (independentCachedEdge 2662)=independentCachedBranchMembers2562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2562
def independentCachedBranchMembers2564 : Finset ℕ := ([12,48,222,1590,1628,1678,1714,1752,1764,2638,2674,2714,2764,2800,3102,3150,3186,3188,3228,3238,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2564 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2564 5 (fun x => (if x<2714 then (if x<1678 then (if x<222 then (if x<48 then 0 else 0) else (if x<1590 then 1 else (if x<1628 then 2 else 1))) else (if x<1764 then (if x<1714 then 0 else (if x<1752 then 0 else 3)) else (if x<2638 then 2 else (if x<2674 then 0 else 0)))) else (if x<3188 then (if x<3102 then (if x<2764 then 3 else (if x<2800 then 1 else 3)) else (if x<3150 then 2 else (if x<3186 then 1 else 4))) else (if x<3274 then (if x<3228 then 2 else (if x<3238 then 1 else 2)) else (if x<3276 then 4 else (if x<3312 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2565 : Finset ℕ := ([12,48,1628,1752,1764,2764,2800,3188,3228,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2565 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2565 4 (fun x => (if x<2764 then (if x<1628 then (if x<48 then 0 else 0) else (if x<1752 then 1 else (if x<1764 then 2 else 1))) else (if x<3228 then (if x<2800 then 0 else (if x<3188 then 0 else 1)) else (if x<3276 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2566 : Finset ℕ := ([12,48,222,1590,1626,1628,1678,1714,1752,1764,2638,2674,2714,2764,2800,3102,3150,3186,3188,3228,3238,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2566 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2566 1626 4
  · have he : independentCachedBranchMembers2566.erase 1626=independentCachedBranchMembers2564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2564
  · have he : independentCachedBranchMembers2566.filter (independentCachedEdge 1626)=independentCachedBranchMembers2565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2565
def independentCachedBranchMembers2567 : Finset ℕ := ([12,48,1590,1628,2638,2674,2714,2764,2800,3102,3188,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2567 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2567 4 (fun x => (if x<2714 then (if x<1628 then (if x<48 then 0 else (if x<1590 then 0 else 1)) else (if x<2638 then 1 else (if x<2674 then 0 else 0))) else (if x<3102 then (if x<2764 then 2 else (if x<2800 then 1 else 2)) else (if x<3228 then (if x<3188 then 2 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2568 : Finset ℕ := ([12,48,222,1590,1626,1628,1678,1714,1752,1764,2638,2674,2714,2764,2800,3102,3150,3186,3188,3226,3228,3238,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2568 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2568 3226 4
  · have he : independentCachedBranchMembers2568.erase 3226=independentCachedBranchMembers2566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2566
  · have he : independentCachedBranchMembers2568.filter (independentCachedEdge 3226)=independentCachedBranchMembers2567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2567
def independentCachedBranchMembers2569 : Finset ℕ := ([12,1628,1714,1764,2638,2714,2764,3102,3186,3228,3238,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2569 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2569 4 (fun x => (if x<2764 then (if x<1764 then (if x<1628 then 0 else (if x<1714 then 0 else 1)) else (if x<2638 then 1 else (if x<2714 then 0 else 1))) else (if x<3228 then (if x<3102 then 1 else (if x<3186 then 0 else 2)) else (if x<3274 then (if x<3238 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2570 : Finset ℕ := ([12,48,222,1590,1626,1628,1678,1714,1752,1764,2638,2674,2714,2762,2764,2800,3102,3150,3186,3188,3226,3228,3238,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2570 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2570 2762 4
  · have he : independentCachedBranchMembers2570.erase 2762=independentCachedBranchMembers2568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2568
  · have he : independentCachedBranchMembers2570.filter (independentCachedEdge 2762)=independentCachedBranchMembers2569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2569
def independentCachedBranchMembers2571 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1652,1678,1692,1702,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2738,2740,2762,2764,2776,2786,2800,3102,3150,3164,3186,3188,3226,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2571 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2571 1702 5
  · have he : independentCachedBranchMembers2571.erase 1702=independentCachedBranchMembers2563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2563
  · have he : independentCachedBranchMembers2571.filter (independentCachedEdge 1702)=independentCachedBranchMembers2570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2570
def independentCachedBranchMembers2572 : Finset ℕ := ([72,222,1590,1626,1652,1678,1692,1714,1740,1776,2638,2652,2674,2714,2740,2762,2776,3102,3150,3164,3186,3226,3238,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2572 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2572 5 (fun x => (if x<2714 then (if x<1692 then (if x<1626 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1652 then 0 else (if x<1678 then 2 else 1))) else (if x<1776 then (if x<1714 then 2 else (if x<1740 then 2 else 0)) else (if x<2652 then (if x<2638 then 3 else 0) else (if x<2674 then 2 else 1)))) else (if x<3164 then (if x<2776 then (if x<2740 then 2 else (if x<2762 then 2 else 1)) else (if x<3102 then 0 else (if x<3150 then 3 else 4))) else (if x<3238 then (if x<3186 then 0 else (if x<3226 then 3 else 4)) else (if x<3274 then (if x<3252 then 4 else 3) else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2573 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1692,1702,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2738,2740,2762,2764,2776,2786,2800,3102,3150,3164,3186,3188,3226,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2573 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2573 1650 5
  · have he : independentCachedBranchMembers2573.erase 1650=independentCachedBranchMembers2571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2571
  · have he : independentCachedBranchMembers2573.filter (independentCachedEdge 1650)=independentCachedBranchMembers2572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2572
def independentCachedBranchMembers2574 : Finset ℕ := ([48,72,222,1590,1614,1626,1652,1678,1740,1752,2614,2638,2650,2702,2714,2740,2764,2776,2786,3102,3164,3186,3228,3238,3250,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2574 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2574 5 (fun x => (if x<2702 then (if x<1652 then (if x<1590 then (if x<72 then 0 else (if x<222 then 0 else 1)) else (if x<1614 then 0 else (if x<1626 then 0 else 1))) else (if x<1752 then (if x<1678 then 2 else (if x<1740 then 1 else 2)) else (if x<2638 then (if x<2614 then 3 else 2) else (if x<2650 then 1 else 3)))) else (if x<3164 then (if x<2764 then (if x<2714 then 2 else (if x<2740 then 1 else 0)) else (if x<2786 then (if x<2776 then 0 else 4) else (if x<3102 then 4 else 1))) else (if x<3238 then (if x<3186 then 3 else (if x<3228 then 2 else 4)) else (if x<3274 then (if x<3250 then 4 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2575 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1692,1702,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2738,2740,2762,2764,2776,2786,2800,3102,3150,3164,3186,3188,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2575 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2575 3298 5
  · have he : independentCachedBranchMembers2575.erase 3298=independentCachedBranchMembers2573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2573
  · have he : independentCachedBranchMembers2575.filter (independentCachedEdge 3298)=independentCachedBranchMembers2574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2574
def independentCachedBranchMembers2576 : Finset ℕ := ([72,1590,1626,1628,1678,1714,1752,1764,2614,2650,2652,2662,2702,2738,2740,2776,2786,3102,3150,3186,3188,3226,3228,3238,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2576 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2576 5 (fun x => (if x<2738 then (if x<1752 then (if x<1628 then (if x<1590 then 0 else (if x<1626 then 0 else 0)) else (if x<1678 then 1 else (if x<1714 then 1 else 2))) else (if x<2650 then (if x<1764 then 2 else (if x<2614 then 1 else 2)) else (if x<2662 then (if x<2652 then 3 else 2) else (if x<2702 then 3 else 3)))) else (if x<3188 then (if x<2786 then (if x<2740 then 3 else (if x<2776 then 0 else 0)) else (if x<3150 then (if x<3102 then 4 else 1) else (if x<3186 then 3 else 3))) else (if x<3238 then (if x<3226 then 1 else (if x<3228 then 3 else 4)) else (if x<3276 then (if x<3274 then 0 else 0) else (if x<3312 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2577 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1692,1702,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2738,2740,2762,2764,2776,2786,2800,3102,3150,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2577 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2577 3214 5
  · have he : independentCachedBranchMembers2577.erase 3214=independentCachedBranchMembers2575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2575
  · have he : independentCachedBranchMembers2577.filter (independentCachedEdge 3214)=independentCachedBranchMembers2576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2576
def independentCachedBranchMembers2578 : Finset ℕ := ([12,48,1590,1626,1652,1678,1692,1714,1740,1776,2614,2650,2662,2702,2738,2764,2786,2800,3102,3150,3164,3186,3226,3238,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2578 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2578 5 (fun x => (if x<2702 then (if x<1692 then (if x<1626 then (if x<48 then 0 else (if x<1590 then 0 else 1)) else (if x<1652 then 1 else (if x<1678 then 2 else 0))) else (if x<1776 then (if x<1714 then 1 else (if x<1740 then 0 else 2)) else (if x<2650 then (if x<2614 then 1 else 2) else (if x<2662 then 3 else 3)))) else (if x<3164 then (if x<2786 then (if x<2738 then 2 else (if x<2764 then 3 else 0)) else (if x<3102 then (if x<2800 then 4 else 0) else (if x<3150 then 1 else 0))) else (if x<3238 then (if x<3186 then 4 else (if x<3226 then 0 else 3)) else (if x<3274 then (if x<3252 then 3 else 1) else (if x<3288 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2579 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1692,1702,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2738,2740,2762,2764,2776,2786,2800,3102,3150,3162,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2579 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2579 3162 5
  · have he : independentCachedBranchMembers2579.erase 3162=independentCachedBranchMembers2577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2577
  · have he : independentCachedBranchMembers2579.filter (independentCachedEdge 3162)=independentCachedBranchMembers2578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2578
def independentCachedBranchMembers2580 : Finset ℕ := ([12,48,72,222,1614,1628,1650,1678,1714,1738,1752,1764,2650,2662,2714,2740,2764,2786,2800,3150,3186,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2580 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2580 5 (fun x => (if x<2650 then (if x<1650 then (if x<222 then (if x<48 then 0 else (if x<72 then 0 else 1)) else (if x<1614 then 1 else (if x<1628 then 0 else 1))) else (if x<1738 then (if x<1678 then 0 else (if x<1714 then 2 else 2)) else (if x<1752 then 1 else (if x<1764 then 2 else 2)))) else (if x<2800 then (if x<2740 then (if x<2662 then 1 else (if x<2714 then 3 else 2)) else (if x<2764 then 3 else (if x<2786 then 0 else 4))) else (if x<3228 then (if x<3150 then 0 else (if x<3186 then 1 else 4)) else (if x<3274 then (if x<3250 then 3 else 0) else (if x<3288 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2581 : Finset ℕ := ([48,72,1628,1650,1678,1752,2650,2800,3150,3228,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2581 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2581 4 (fun x => (if x<2650 then (if x<1650 then (if x<72 then 0 else (if x<1628 then 0 else 1)) else (if x<1678 then 1 else (if x<1752 then 2 else 2))) else (if x<3228 then (if x<2800 then 1 else (if x<3150 then 2 else 0)) else (if x<3250 then 3 else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2582 : Finset ℕ := ([12,48,72,222,1614,1628,1650,1678,1692,1714,1738,1752,1764,2650,2662,2714,2740,2764,2786,2800,3150,3186,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2582 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2582 1692 4
  · have he : independentCachedBranchMembers2582.erase 1692=independentCachedBranchMembers2580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2580
  · have he : independentCachedBranchMembers2582.filter (independentCachedEdge 1692)=independentCachedBranchMembers2581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2581
def independentCachedBranchMembers2583 : Finset ℕ := ([12,222,1650,1714,1738,1752,2650,2714,2786,2800,3150,3228] : List ℕ).toFinset
theorem independentCachedBranchBound2583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2583 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2583 4 (fun x => (if x<2650 then (if x<1714 then (if x<222 then 0 else (if x<1650 then 0 else 1)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<2800 then (if x<2714 then 1 else (if x<2786 then 2 else 1)) else (if x<3150 then 2 else (if x<3228 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2584 : Finset ℕ := ([12,48,72,222,1590,1614,1628,1650,1678,1692,1714,1738,1752,1764,2650,2662,2714,2740,2764,2786,2800,3150,3186,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2584 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2584 1590 4
  · have he : independentCachedBranchMembers2584.erase 1590=independentCachedBranchMembers2582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2582
  · have he : independentCachedBranchMembers2584.filter (independentCachedEdge 1590)=independentCachedBranchMembers2583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2583
def independentCachedBranchMembers2585 : Finset ℕ := ([72,1590,1628,1678,1714,1752,1764,2650,2662,2740,2786,3150,3186,3228,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2585 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2585 4 (fun x => (if x<2650 then (if x<1678 then (if x<1590 then 0 else (if x<1628 then 0 else 0)) else (if x<1752 then (if x<1714 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3150 then (if x<2740 then (if x<2662 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3228 then (if x<3186 then 2 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2586 : Finset ℕ := ([12,48,72,222,1590,1614,1628,1650,1678,1692,1714,1738,1752,1764,2650,2662,2714,2740,2764,2786,2800,3150,3186,3214,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2586 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2586 3214 4
  · have he : independentCachedBranchMembers2586.erase 3214=independentCachedBranchMembers2584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2584
  · have he : independentCachedBranchMembers2586.filter (independentCachedEdge 3214)=independentCachedBranchMembers2585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2585
def independentCachedBranchMembers2587 : Finset ℕ := ([48,1590,1628,1650,1678,1738,1764,2662,2714,2740,2800,3150,3228,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2587 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2587 4 (fun x => (if x<2662 then (if x<1650 then (if x<1590 then 0 else (if x<1628 then 0 else 1)) else (if x<1738 then (if x<1678 then 1 else 0) else (if x<1764 then 1 else 1))) else (if x<3150 then (if x<2740 then (if x<2714 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3250 then (if x<3228 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2588 : Finset ℕ := ([12,48,72,222,1590,1614,1628,1650,1678,1692,1714,1738,1752,1764,2650,2662,2714,2740,2764,2786,2800,3150,3164,3186,3214,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2588 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2588 3164 4
  · have he : independentCachedBranchMembers2588.erase 3164=independentCachedBranchMembers2586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2586
  · have he : independentCachedBranchMembers2588.filter (independentCachedEdge 3164)=independentCachedBranchMembers2587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2587
def independentCachedBranchMembers2589 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1692,1702,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2738,2740,2762,2764,2776,2786,2788,2800,3102,3150,3162,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2589 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2589 2788 5
  · have he : independentCachedBranchMembers2589.erase 2788=independentCachedBranchMembers2579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2579
  · have he : independentCachedBranchMembers2589.filter (independentCachedEdge 2788)=independentCachedBranchMembers2588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2588
def independentCachedBranchMembers2590 : Finset ℕ := ([48,72,1590,1614,1692,1702,1714,1738,1764,1776,2652,2662,2674,2702,2714,2740,2764,2776,2786,3150,3162,3188,3228,3238,3250,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2590 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2590 5 (fun x => (if x<2702 then (if x<1714 then (if x<1614 then (if x<72 then 0 else (if x<1590 then 0 else 0)) else (if x<1692 then 0 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1764 then 1 else 2)) else (if x<2662 then (if x<2652 then 1 else 3) else (if x<2674 then 3 else 4)))) else (if x<3162 then (if x<2764 then (if x<2714 then 1 else (if x<2740 then 2 else 0)) else (if x<2786 then (if x<2776 then 0 else 1) else (if x<3150 then 1 else 3))) else (if x<3238 then (if x<3188 then 4 else (if x<3228 then 3 else 3)) else (if x<3274 then (if x<3250 then 3 else 0) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2591 : Finset ℕ := ([72,1590,1738,1776,2764,2776,2786,3150,3162,3188,3228,3238,3250] : List ℕ).toFinset
theorem independentCachedBranchBound2591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2591 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2591 4 (fun x => (if x<2786 then (if x<1776 then (if x<1590 then 0 else (if x<1738 then 0 else 1)) else (if x<2764 then 1 else (if x<2776 then 0 else 1))) else (if x<3188 then (if x<3150 then 1 else (if x<3162 then 2 else 3)) else (if x<3238 then (if x<3228 then 2 else 2) else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2592 : Finset ℕ := ([72,1776,2776,3150,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound2592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2592 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2592 3 (fun x => (if x<3150 then (if x<1776 then 0 else (if x<2776 then 1 else 0)) else (if x<3228 then 1 else (if x<3250 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2593 : Finset ℕ := ([72,1590,1738,1764,1776,2764,2776,2786,3150,3162,3188,3228,3238,3250] : List ℕ).toFinset
theorem independentCachedBranchBound2593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2593 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2593 1764 3
  · have he : independentCachedBranchMembers2593.erase 1764=independentCachedBranchMembers2591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2591
  · have he : independentCachedBranchMembers2593.filter (independentCachedEdge 1764)=independentCachedBranchMembers2592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2592
def independentCachedBranchMembers2594 : Finset ℕ := ([48,72,1590,1614,1652,1692,1702,1714,1738,1764,1776,2652,2662,2674,2702,2714,2740,2764,2776,2786,3150,3162,3188,3228,3238,3250,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2594 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2594 1652 4
  · have he : independentCachedBranchMembers2594.erase 1652=independentCachedBranchMembers2590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2590
  · have he : independentCachedBranchMembers2594.filter (independentCachedEdge 1652)=independentCachedBranchMembers2593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2593
def independentCachedBranchMembers2595 : Finset ℕ := ([48,1614,1702,1738,1764,2662,2702,2764,2786,3162,3188,3228,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2595 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2595 4 (fun x => (if x<2764 then (if x<1738 then (if x<1614 then 0 else (if x<1702 then 0 else 1)) else (if x<2662 then (if x<1764 then 1 else 2) else (if x<2702 then 2 else 0))) else (if x<3188 then (if x<2786 then 2 else (if x<3162 then 1 else 3)) else (if x<3250 then (if x<3228 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2596 : Finset ℕ := ([48,72,1590,1614,1626,1652,1692,1702,1714,1738,1764,1776,2652,2662,2674,2702,2714,2740,2764,2776,2786,3150,3162,3188,3228,3238,3250,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2596 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2596 1626 4
  · have he : independentCachedBranchMembers2596.erase 1626=independentCachedBranchMembers2594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2594
  · have he : independentCachedBranchMembers2596.filter (independentCachedEdge 1626)=independentCachedBranchMembers2595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2595
def independentCachedBranchMembers2597 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1692,1702,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2716,2738,2740,2762,2764,2776,2786,2788,2800,3102,3150,3162,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2597 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2597 2716 5
  · have he : independentCachedBranchMembers2597.erase 2716=independentCachedBranchMembers2589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2589
  · have he : independentCachedBranchMembers2597.filter (independentCachedEdge 2716)=independentCachedBranchMembers2596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2596
def independentCachedBranchMembers2598 : Finset ℕ := ([48,72,1628,1650,1692,1702,1714,1738,1764,1776,2614,2650,2702,2740,2764,2786,3150,3162,3188,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2598 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2598 5 (fun x => (if x<2702 then (if x<1714 then (if x<1650 then (if x<72 then 0 else (if x<1628 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 2 else 2))) else (if x<1776 then (if x<1738 then 0 else (if x<1764 then 0 else 1)) else (if x<2614 then 2 else (if x<2650 then 0 else 1)))) else (if x<3188 then (if x<2786 then (if x<2740 then 2 else (if x<2764 then 2 else 1)) else (if x<3150 then 1 else (if x<3162 then 3 else 4))) else (if x<3276 then (if x<3214 then 3 else (if x<3252 then 4 else 0)) else (if x<3288 then 0 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2599 : Finset ℕ := ([48,72,1628,1650,1702,1776,2650,2702,3150,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2599 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2599 4 (fun x => (if x<2650 then (if x<1650 then (if x<72 then 0 else (if x<1628 then 0 else 1)) else (if x<1702 then 1 else (if x<1776 then 2 else 2))) else (if x<3252 then (if x<2702 then 1 else (if x<3150 then 2 else 0)) else (if x<3276 then 3 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2600 : Finset ℕ := ([48,72,1628,1650,1692,1702,1714,1738,1764,1776,2614,2650,2702,2714,2740,2764,2786,3150,3162,3188,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2600 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2600 2714 4
  · have he : independentCachedBranchMembers2600.erase 2714=independentCachedBranchMembers2598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2598
  · have he : independentCachedBranchMembers2600.filter (independentCachedEdge 2714)=independentCachedBranchMembers2599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2599
def independentCachedBranchMembers2601 : Finset ℕ := ([1650,1692,1702,1764,2650,2702,2740,2764,3150,3188,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2601 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2601 4 (fun x => (if x<2740 then (if x<1764 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<2650 then 1 else (if x<2702 then 0 else 0))) else (if x<3188 then (if x<2764 then 1 else (if x<3150 then 1 else 2)) else (if x<3288 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2602 : Finset ℕ := ([48,72,1628,1650,1692,1702,1714,1738,1764,1776,2614,2638,2650,2702,2714,2740,2764,2786,3150,3162,3188,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2602 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2602 2638 4
  · have he : independentCachedBranchMembers2602.erase 2638=independentCachedBranchMembers2600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2600
  · have he : independentCachedBranchMembers2602.filter (independentCachedEdge 2638)=independentCachedBranchMembers2601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2601
def independentCachedBranchMembers2603 : Finset ℕ := ([48,1650,1702,1714,1764,1776,2614,2740,2786,3188,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2603 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2603 4 (fun x => (if x<2614 then (if x<1714 then (if x<1650 then 0 else (if x<1702 then 0 else 1)) else (if x<1764 then 2 else (if x<1776 then 2 else 1))) else (if x<3188 then (if x<2740 then 0 else (if x<2786 then 1 else 1)) else (if x<3252 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2604 : Finset ℕ := ([48,72,222,1628,1650,1692,1702,1714,1738,1764,1776,2614,2638,2650,2702,2714,2740,2764,2786,3150,3162,3188,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2604 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2604 222 4
  · have he : independentCachedBranchMembers2604.erase 222=independentCachedBranchMembers2602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2602
  · have he : independentCachedBranchMembers2604.filter (independentCachedEdge 222)=independentCachedBranchMembers2603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2603
def independentCachedBranchMembers2605 : Finset ℕ := ([48,1650,1714,1764,2614,2650,2714,2764,3150,3188,3214,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2605 4 (fun x => (if x<2764 then (if x<1764 then (if x<1650 then 0 else (if x<1714 then 0 else 1)) else (if x<2650 then (if x<2614 then 1 else 0) else (if x<2714 then 2 else 1))) else (if x<3214 then (if x<3150 then 1 else (if x<3188 then 2 else 0)) else (if x<3288 then (if x<3252 then 3 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2606 : Finset ℕ := ([48,72,222,1628,1650,1692,1702,1714,1738,1764,1776,2614,2638,2650,2702,2714,2740,2764,2776,2786,3150,3162,3188,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2606 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2606 2776 4
  · have he : independentCachedBranchMembers2606.erase 2776=independentCachedBranchMembers2604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2604
  · have he : independentCachedBranchMembers2606.filter (independentCachedEdge 2776)=independentCachedBranchMembers2605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2605
def independentCachedBranchMembers2607 : Finset ℕ := ([72,1628,1650,1702,1776,2614,2638,2714,2740,2764,2786,3162,3188,3214,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2607 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2607 4 (fun x => (if x<2714 then (if x<1702 then (if x<1628 then 0 else (if x<1650 then 0 else 1)) else (if x<2614 then (if x<1776 then 1 else 2) else (if x<2638 then 1 else 0))) else (if x<3162 then (if x<2764 then (if x<2740 then 3 else 2) else (if x<2786 then 3 else 1)) else (if x<3214 then (if x<3188 then 0 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2608 : Finset ℕ := ([1628,1702,2714,2786,3162,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2608 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2608 3 (fun x => (if x<2786 then (if x<1702 then 0 else (if x<2714 then 1 else 2)) else (if x<3162 then 0 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2609 : Finset ℕ := ([48,72,1628,1650,1702,1776,2614,2638,2714,2740,2764,2786,3162,3188,3214,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2609 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2609 48 3
  · have he : independentCachedBranchMembers2609.erase 48=independentCachedBranchMembers2607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2607
  · have he : independentCachedBranchMembers2609.filter (independentCachedEdge 48)=independentCachedBranchMembers2608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2608
def independentCachedBranchMembers2610 : Finset ℕ := ([48,72,222,1628,1650,1692,1702,1714,1738,1764,1776,2614,2638,2650,2702,2714,2740,2764,2776,2786,3150,3162,3188,3214,3226,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2610 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2610 3226 4
  · have he : independentCachedBranchMembers2610.erase 3226=independentCachedBranchMembers2606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2606
  · have he : independentCachedBranchMembers2610.filter (independentCachedEdge 3226)=independentCachedBranchMembers2609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2609
def independentCachedBranchMembers2611 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1692,1702,1714,1738,1740,1752,1762,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2716,2738,2740,2762,2764,2776,2786,2788,2800,3102,3150,3162,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2611 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2611 1762 5
  · have he : independentCachedBranchMembers2611.erase 1762=independentCachedBranchMembers2597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2597
  · have he : independentCachedBranchMembers2611.filter (independentCachedEdge 1762)=independentCachedBranchMembers2610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2610
def independentCachedBranchMembers2612 : Finset ℕ := ([48,72,1626,1652,1678,1692,1714,1738,1752,1764,2614,2652,2714,2740,2764,2800,3150,3164,3186,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2612 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2612 5 (fun x => (if x<2714 then (if x<1714 then (if x<1652 then (if x<72 then 0 else (if x<1626 then 0 else 1)) else (if x<1678 then 1 else (if x<1692 then 2 else 1))) else (if x<1764 then (if x<1738 then 0 else (if x<1752 then 0 else 2)) else (if x<2614 then 2 else (if x<2652 then 0 else 1)))) else (if x<3186 then (if x<2800 then (if x<2740 then 1 else (if x<2764 then 1 else 2)) else (if x<3150 then 2 else (if x<3164 then 3 else 4))) else (if x<3252 then (if x<3226 then 3 else (if x<3238 then 3 else 3)) else (if x<3276 then 0 else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2613 : Finset ℕ := ([48,72,1626,1652,1678,1752,2652,2800,3150,3226,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2613 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2613 4 (fun x => (if x<2652 then (if x<1652 then (if x<72 then 0 else (if x<1626 then 0 else 1)) else (if x<1678 then 1 else (if x<1752 then 2 else 2))) else (if x<3226 then (if x<2800 then 1 else (if x<3150 then 2 else 0)) else (if x<3252 then 3 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2614 : Finset ℕ := ([48,72,1626,1652,1678,1692,1714,1738,1752,1764,2614,2652,2714,2740,2764,2786,2800,3150,3164,3186,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2614 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2614 2786 4
  · have he : independentCachedBranchMembers2614.erase 2786=independentCachedBranchMembers2612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2612
  · have he : independentCachedBranchMembers2614.filter (independentCachedEdge 2786)=independentCachedBranchMembers2613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2613
def independentCachedBranchMembers2615 : Finset ℕ := ([1652,1692,1752,1764,2652,2740,2764,2800,3150,3186,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2615 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2615 4 (fun x => (if x<2764 then (if x<1764 then (if x<1692 then 0 else (if x<1752 then 0 else 1)) else (if x<2652 then 1 else (if x<2740 then 0 else 0))) else (if x<3186 then (if x<2800 then 1 else (if x<3150 then 1 else 2)) else (if x<3226 then 2 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2616 : Finset ℕ := ([48,72,1626,1652,1678,1692,1714,1738,1752,1764,2614,2638,2652,2714,2740,2764,2786,2800,3150,3164,3186,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2616 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2616 2638 4
  · have he : independentCachedBranchMembers2616.erase 2638=independentCachedBranchMembers2614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2614
  · have he : independentCachedBranchMembers2616.filter (independentCachedEdge 2638)=independentCachedBranchMembers2615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2615
def independentCachedBranchMembers2617 : Finset ℕ := ([72,1626,1652,1738,1752,1764,2614,2714,2740,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2617 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2617 4 (fun x => (if x<2614 then (if x<1738 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<1752 then 2 else (if x<1764 then 1 else 2))) else (if x<3226 then (if x<2714 then 1 else (if x<2740 then 1 else 0)) else (if x<3238 then 2 else (if x<3252 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2618 : Finset ℕ := ([12,48,72,1626,1652,1678,1692,1714,1738,1752,1764,2614,2638,2652,2714,2740,2764,2786,2800,3150,3164,3186,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2618 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2618 12 4
  · have he : independentCachedBranchMembers2618.erase 12=independentCachedBranchMembers2616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2616
  · have he : independentCachedBranchMembers2618.filter (independentCachedEdge 12)=independentCachedBranchMembers2617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2617
def independentCachedBranchMembers2619 : Finset ℕ := ([72,1738,1752,1764,2614,2764,2786,2800,3150,3164,3186,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2619 4 (fun x => (if x<2800 then (if x<1764 then (if x<1738 then 0 else (if x<1752 then 0 else 1)) else (if x<2764 then (if x<2614 then 1 else 0) else (if x<2786 then 1 else 2))) else (if x<3186 then (if x<3150 then 1 else (if x<3164 then 3 else 2)) else (if x<3238 then (if x<3226 then 2 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2620 : Finset ℕ := ([12,48,72,1626,1652,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2714,2740,2764,2786,2800,3150,3164,3186,3226,3238,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2620 2674 4
  · have he : independentCachedBranchMembers2620.erase 2674=independentCachedBranchMembers2618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2618
  · have he : independentCachedBranchMembers2620.filter (independentCachedEdge 2674)=independentCachedBranchMembers2619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2619
def independentCachedBranchMembers2621 : Finset ℕ := ([72,1626,1652,1678,1752,2614,2638,2714,2740,2764,2786,3164,3186,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2621 4 (fun x => (if x<2714 then (if x<1678 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<2614 then (if x<1752 then 2 else 1) else (if x<2638 then 1 else 0))) else (if x<3164 then (if x<2764 then (if x<2740 then 1 else 3) else (if x<2786 then 2 else 3)) else (if x<3238 then (if x<3186 then 0 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2622 : Finset ℕ := ([1626,1752,2714,2786,3164,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2622 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2622 3 (fun x => (if x<2786 then (if x<1752 then 0 else (if x<2714 then 1 else 0)) else (if x<3164 then 2 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2623 : Finset ℕ := ([48,72,1626,1652,1678,1752,2614,2638,2714,2740,2764,2786,3164,3186,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2623 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2623 48 3
  · have he : independentCachedBranchMembers2623.erase 48=independentCachedBranchMembers2621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2621
  · have he : independentCachedBranchMembers2623.filter (independentCachedEdge 48)=independentCachedBranchMembers2622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2622
def independentCachedBranchMembers2624 : Finset ℕ := ([12,48,72,1626,1652,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2714,2740,2764,2786,2800,3150,3164,3186,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2624 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2624 3298 4
  · have he : independentCachedBranchMembers2624.erase 3298=independentCachedBranchMembers2620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2620
  · have he : independentCachedBranchMembers2624.filter (independentCachedEdge 3298)=independentCachedBranchMembers2623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2623
def independentCachedBranchMembers2625 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1690,1692,1702,1714,1738,1740,1752,1762,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2716,2738,2740,2762,2764,2776,2786,2788,2800,3102,3150,3162,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2625 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2625 1690 5
  · have he : independentCachedBranchMembers2625.erase 1690=independentCachedBranchMembers2611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2611
  · have he : independentCachedBranchMembers2625.filter (independentCachedEdge 1690)=independentCachedBranchMembers2624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2624
def independentCachedBranchMembers2626 : Finset ℕ := ([12,222,1590,1614,1626,1628,1678,1690,1692,1762,1776,2614,2638,2650,2652,2702,2716,2788,2800,3102,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2626 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2626 5 (fun x => (if x<2652 then (if x<1690 then (if x<1614 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then (if x<1626 then 0 else 1) else (if x<1678 then 2 else 1))) else (if x<1776 then (if x<1692 then 2 else (if x<1762 then 0 else 1)) else (if x<2638 then (if x<2614 then 2 else 3) else (if x<2650 then 3 else 4)))) else (if x<3188 then (if x<2788 then (if x<2702 then 0 else (if x<2716 then 0 else 3)) else (if x<3102 then (if x<2800 then 3 else 4) else (if x<3186 then 0 else 1))) else (if x<3252 then (if x<3238 then 2 else (if x<3250 then 1 else 2)) else (if x<3276 then (if x<3274 then 3 else 1) else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2627 : Finset ℕ := ([222,1590,1614,1626,1678,1690,1762,2652,2716,2788,2800,3188,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2627 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2627 4 (fun x => (if x<2652 then (if x<1626 then (if x<1590 then 0 else (if x<1614 then 1 else 0)) else (if x<1690 then (if x<1678 then 1 else 1) else (if x<1762 then 0 else 1))) else (if x<3188 then (if x<2788 then (if x<2716 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3276 then (if x<3252 then 2 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2628 : Finset ℕ := ([12,222,1590,1614,1626,1628,1678,1690,1692,1762,1776,2614,2638,2650,2652,2702,2716,2786,2788,2800,3102,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2628 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2628 2786 4
  · have he : independentCachedBranchMembers2628.erase 2786=independentCachedBranchMembers2626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2626
  · have he : independentCachedBranchMembers2628.filter (independentCachedEdge 2786)=independentCachedBranchMembers2627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2627
def independentCachedBranchMembers2629 : Finset ℕ := ([12,1590,1614,1628,1690,1762,1776,2650,2702,2716,2788,3186,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2629 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2629 4 (fun x => (if x<2650 then (if x<1628 then (if x<1590 then 0 else (if x<1614 then 1 else 0)) else (if x<1762 then (if x<1690 then 1 else 1) else (if x<1776 then 0 else 1))) else (if x<3186 then (if x<2716 then (if x<2702 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3252 then (if x<3238 then 2 else 2) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2630 : Finset ℕ := ([12,222,1590,1614,1626,1628,1678,1690,1692,1762,1776,2614,2638,2650,2652,2702,2714,2716,2786,2788,2800,3102,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2630 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2630 2714 4
  · have he : independentCachedBranchMembers2630.erase 2714=independentCachedBranchMembers2628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2628
  · have he : independentCachedBranchMembers2630.filter (independentCachedEdge 2714)=independentCachedBranchMembers2629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2629
def independentCachedBranchMembers2631 : Finset ℕ := ([222,1626,1690,1762,1776,2614,2638,2652,2702,2716,2788,3186,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2631 4 (fun x => (if x<2652 then (if x<1762 then (if x<1626 then 0 else (if x<1690 then 0 else 1)) else (if x<2614 then (if x<1776 then 1 else 2) else (if x<2638 then 3 else 0))) else (if x<3186 then (if x<2716 then (if x<2702 then 3 else 2) else (if x<2788 then 1 else 1)) else (if x<3274 then (if x<3250 then 2 else 3) else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2632 : Finset ℕ := ([1626,1690,2614,2788,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2632 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2632 3 (fun x => (if x<2788 then (if x<1690 then 0 else (if x<2614 then 1 else 2)) else (if x<3274 then 0 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2633 : Finset ℕ := ([12,222,1626,1690,1762,1776,2614,2638,2652,2702,2716,2788,3186,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2633 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2633 12 3
  · have he : independentCachedBranchMembers2633.erase 12=independentCachedBranchMembers2631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2631
  · have he : independentCachedBranchMembers2633.filter (independentCachedEdge 12)=independentCachedBranchMembers2632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2632
def independentCachedBranchMembers2634 : Finset ℕ := ([12,222,1590,1614,1626,1628,1678,1690,1692,1762,1764,1776,2614,2638,2650,2652,2702,2714,2716,2786,2788,2800,3102,3186,3188,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2634 1764 4
  · have he : independentCachedBranchMembers2634.erase 1764=independentCachedBranchMembers2630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2630
  · have he : independentCachedBranchMembers2634.filter (independentCachedEdge 1764)=independentCachedBranchMembers2633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2633
def independentCachedBranchMembers2635 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1690,1692,1702,1714,1738,1740,1752,1762,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2716,2738,2740,2762,2764,2776,2786,2788,2800,3102,3126,3150,3162,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2635 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2635 3126 5
  · have he : independentCachedBranchMembers2635.erase 3126=independentCachedBranchMembers2625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2625
  · have he : independentCachedBranchMembers2635.filter (independentCachedEdge 3126)=independentCachedBranchMembers2634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2634
def independentCachedBranchMembers2636 : Finset ℕ := ([12,48,72,222,1614,1628,1650,1678,1714,1738,1752,1764,2614,2638,2652,2702,2716,2738,2762,2776,2788,3102,3162,3188,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2636 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2636 5 (fun x => (if x<2702 then (if x<1678 then (if x<222 then (if x<48 then 0 else (if x<72 then 0 else 1)) else (if x<1628 then (if x<1614 then 1 else 0) else (if x<1650 then 1 else 0))) else (if x<1764 then (if x<1738 then (if x<1714 then 2 else 2) else (if x<1752 then 1 else 2)) else (if x<2638 then (if x<2614 then 2 else 3) else (if x<2652 then 1 else 3)))) else (if x<3162 then (if x<2762 then (if x<2716 then 0 else (if x<2738 then 4 else 0)) else (if x<2788 then (if x<2776 then 4 else 1) else (if x<3102 then 3 else 3))) else (if x<3252 then (if x<3226 then (if x<3188 then 1 else 3) else (if x<3238 then 2 else 2)) else (if x<3298 then (if x<3276 then 4 else 0) else (if x<3312 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2637 : Finset ℕ := ([72,222,1614,1628,1650,1738,1752,1764,2614,2702,2716,2738,3102,3226,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2637 4 (fun x => (if x<2614 then (if x<1650 then (if x<1614 then (if x<222 then 0 else 0) else (if x<1628 then 0 else 1)) else (if x<1752 then (if x<1738 then 1 else 1) else (if x<1764 then 0 else 1))) else (if x<3102 then (if x<2716 then (if x<2702 then 2 else 2) else (if x<2738 then 3 else 3)) else (if x<3238 then (if x<3226 then 2 else 3) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2638 : Finset ℕ := ([12,48,72,222,1614,1628,1650,1678,1714,1738,1752,1764,2614,2638,2652,2674,2702,2716,2738,2762,2776,2788,3102,3162,3188,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2638 2674 4
  · have he : independentCachedBranchMembers2638.erase 2674=independentCachedBranchMembers2636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2636
  · have he : independentCachedBranchMembers2638.filter (independentCachedEdge 2674)=independentCachedBranchMembers2637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2637
def independentCachedBranchMembers2639 : Finset ℕ := ([72,1628,1650,1678,1752,2614,2638,2716,2738,2762,2788,3162,3188,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2639 4 (fun x => (if x<2716 then (if x<1678 then (if x<1628 then 0 else (if x<1650 then 0 else 1)) else (if x<2614 then (if x<1752 then 2 else 1) else (if x<2638 then 1 else 0))) else (if x<3162 then (if x<2762 then (if x<2738 then 1 else 3) else (if x<2788 then 2 else 3)) else (if x<3238 then (if x<3188 then 0 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2640 : Finset ℕ := ([1628,1752,2716,2788,3162,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2640 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2640 3 (fun x => (if x<2788 then (if x<1752 then 0 else (if x<2716 then 1 else 0)) else (if x<3162 then 2 else (if x<3238 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2641 : Finset ℕ := ([48,72,1628,1650,1678,1752,2614,2638,2716,2738,2762,2788,3162,3188,3238,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2641 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2641 48 3
  · have he : independentCachedBranchMembers2641.erase 48=independentCachedBranchMembers2639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2639
  · have he : independentCachedBranchMembers2641.filter (independentCachedEdge 48)=independentCachedBranchMembers2640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2640
def independentCachedBranchMembers2642 : Finset ℕ := ([12,48,72,222,1614,1628,1650,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2702,2716,2738,2762,2776,2788,3102,3162,3188,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2642 1692 4
  · have he : independentCachedBranchMembers2642.erase 1692=independentCachedBranchMembers2638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2638
  · have he : independentCachedBranchMembers2642.filter (independentCachedEdge 1692)=independentCachedBranchMembers2641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2641
def independentCachedBranchMembers2643 : Finset ℕ := ([222,1650,1714,1738,1752,2614,2638,2652,2702,2716,2788,3162,3226,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2643 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2643 4 (fun x => (if x<2652 then (if x<1738 then (if x<1650 then 0 else (if x<1714 then 1 else 2)) else (if x<2614 then (if x<1752 then 0 else 1) else (if x<2638 then 1 else 0))) else (if x<3162 then (if x<2716 then (if x<2702 then 2 else 3) else (if x<2788 then 1 else 3)) else (if x<3298 then (if x<3226 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2644 : Finset ℕ := ([1738,1752,2614,2788,3162,3226] : List ℕ).toFinset
theorem independentCachedBranchBound2644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2644 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2644 3 (fun x => (if x<2788 then (if x<1752 then 0 else (if x<2614 then 1 else 0)) else (if x<3162 then 2 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2645 : Finset ℕ := ([12,222,1650,1714,1738,1752,2614,2638,2652,2702,2716,2788,3162,3226,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2645 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2645 12 3
  · have he : independentCachedBranchMembers2645.erase 12=independentCachedBranchMembers2643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2643
  · have he : independentCachedBranchMembers2645.filter (independentCachedEdge 12)=independentCachedBranchMembers2644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2644
def independentCachedBranchMembers2646 : Finset ℕ := ([12,48,72,222,1590,1614,1628,1650,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2702,2716,2738,2762,2776,2788,3102,3162,3188,3226,3238,3252,3276,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2646 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2646 1590 4
  · have he : independentCachedBranchMembers2646.erase 1590=independentCachedBranchMembers2642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2642
  · have he : independentCachedBranchMembers2646.filter (independentCachedEdge 1590)=independentCachedBranchMembers2645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2645
def independentCachedBranchMembers2647 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1650,1652,1678,1690,1692,1702,1714,1738,1740,1752,1762,1764,1776,2614,2638,2650,2652,2662,2674,2702,2714,2716,2738,2740,2762,2764,2776,2786,2788,2800,3102,3126,3150,3162,3164,3186,3188,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2647 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2647 3300 5
  · have he : independentCachedBranchMembers2647.erase 3300=independentCachedBranchMembers2635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2635
  · have he : independentCachedBranchMembers2647.filter (independentCachedEdge 3300)=independentCachedBranchMembers2646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2646
def independentCachedBranchMembers2648 : Finset ℕ := ([12,18,40,48,72,80,130,132,192,222,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2648 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2648 40 6
  · have he : independentCachedBranchMembers2648.erase 40=independentCachedBranchMembers2526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2526
  · have he : independentCachedBranchMembers2648.filter (independentCachedEdge 40)=independentCachedBranchMembers2647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2647
def independentCachedBranchMembers2649 : Finset ℕ := ([1708,1714,1738,1748,2620,2650,2662,2710,2730,2740,2764,2770,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2649 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2649 6 (fun x => (if x<3126 then (if x<2710 then (if x<1748 then (if x<1714 then 0 else (if x<1738 then 0 else 0)) else (if x<2650 then (if x<2620 then 0 else 1) else (if x<2662 then 1 else 1))) else (if x<2764 then (if x<2730 then 1 else (if x<2740 then 0 else 0)) else (if x<2800 then (if x<2770 then 0 else 0) else (if x<3118 then 1 else 2)))) else (if x<3226 then (if x<3178 then (if x<3150 then 3 else (if x<3158 then 3 else 2)) else (if x<3186 then (if x<3180 then 4 else 5) else (if x<3188 then 5 else 4))) else (if x<3270 then (if x<3238 then (if x<3228 then 2 else 3) else (if x<3256 then 4 else 4)) else (if x<3298 then (if x<3288 then 5 else 5) else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2650 : Finset ℕ := ([1714,1748,2710,2730,2764,2800,3118,3150,3186,3188,3226,3228,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2650 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2650 5 (fun x => (if x<3150 then (if x<2730 then (if x<1748 then 0 else (if x<2710 then 0 else 0)) else (if x<2800 then (if x<2764 then 0 else 0) else (if x<3118 then 0 else 1))) else (if x<3226 then (if x<3186 then 2 else (if x<3188 then 1 else 2)) else (if x<3238 then (if x<3228 then 1 else 2) else (if x<3270 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2651 : Finset ℕ := ([1708,1714,1738,1748,2620,2650,2662,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2651 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2651 2792 5
  · have he : independentCachedBranchMembers2651.erase 2792=independentCachedBranchMembers2649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2649
  · have he : independentCachedBranchMembers2651.filter (independentCachedEdge 2792)=independentCachedBranchMembers2650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2650
def independentCachedBranchMembers2652 : Finset ℕ := ([1714,1748,2710,2730,2764,2800,3126,3158,3178,3180,3256,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2652 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2652 5 (fun x => (if x<3158 then (if x<2730 then (if x<1748 then 0 else (if x<2710 then 0 else 0)) else (if x<2800 then (if x<2764 then 0 else 0) else (if x<3126 then 0 else 1))) else (if x<3256 then (if x<3178 then 2 else (if x<3180 then 1 else 2)) else (if x<3298 then (if x<3288 then 1 else 2) else (if x<3300 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2653 : Finset ℕ := ([1708,1714,1738,1748,2620,2650,2662,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2653 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2653 2702 5
  · have he : independentCachedBranchMembers2653.erase 2702=independentCachedBranchMembers2651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2651
  · have he : independentCachedBranchMembers2653.filter (independentCachedEdge 2702)=independentCachedBranchMembers2652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2652
def independentCachedBranchMembers2654 : Finset ℕ := ([1708,1738,2620,2650,2730,2764,3118,3126,3178,3186,3226,3256,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2654 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2654 5 (fun x => (if x<3126 then (if x<2650 then (if x<1738 then 0 else (if x<2620 then 0 else 0)) else (if x<2764 then (if x<2730 then 0 else 0) else (if x<3118 then 0 else 1))) else (if x<3226 then (if x<3178 then 2 else (if x<3186 then 2 else 1)) else (if x<3270 then (if x<3256 then 1 else 2) else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2655 : Finset ℕ := ([1708,1714,1738,1748,2620,2650,2652,2662,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2655 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2655 2652 5
  · have he : independentCachedBranchMembers2655.erase 2652=independentCachedBranchMembers2653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2653
  · have he : independentCachedBranchMembers2655.filter (independentCachedEdge 2652)=independentCachedBranchMembers2654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2654
def independentCachedBranchMembers2656 : Finset ℕ := ([1708,1738,2620,2650,2730,2764,3150,3158,3180,3188,3228,3238,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2656 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2656 5 (fun x => (if x<3158 then (if x<2650 then (if x<1738 then 0 else (if x<2620 then 0 else 0)) else (if x<2764 then (if x<2730 then 0 else 0) else (if x<3150 then 0 else 1))) else (if x<3228 then (if x<3180 then 2 else (if x<3188 then 2 else 1)) else (if x<3288 then (if x<3238 then 1 else 1) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2657 : Finset ℕ := ([1708,1714,1738,1748,2618,2620,2650,2652,2662,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2657 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2657 2618 5
  · have he : independentCachedBranchMembers2657.erase 2618=independentCachedBranchMembers2655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2655
  · have he : independentCachedBranchMembers2657.filter (independentCachedEdge 2618)=independentCachedBranchMembers2656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2656
def independentCachedBranchMembers2658 : Finset ℕ := ([1714,1748,2618,2620,2650,2652,2662,2710,2730,2764,2800,3126,3158,3178,3180,3226,3228,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2658 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2658 5 (fun x => (if x<2764 then (if x<2650 then (if x<2618 then (if x<1748 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2662 then (if x<2652 then 1 else 0) else (if x<2710 then 1 else (if x<2730 then 0 else 1)))) else (if x<3180 then (if x<3126 then (if x<2800 then 1 else 0) else (if x<3158 then 2 else (if x<3178 then 3 else 2))) else (if x<3228 then (if x<3226 then 3 else 2) else (if x<3238 then 3 else (if x<3270 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2659 : Finset ℕ := ([1708,1714,1738,1748,1776,2618,2620,2650,2652,2662,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2659 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2659 1776 5
  · have he : independentCachedBranchMembers2659.erase 1776=independentCachedBranchMembers2657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2657
  · have he : independentCachedBranchMembers2659.filter (independentCachedEdge 1776)=independentCachedBranchMembers2658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2658
def independentCachedBranchMembers2660 : Finset ℕ := ([1714,1748,2618,2620,2650,2652,2662,2710,2730,2764,2800,3118,3150,3186,3188,3256,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2660 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2660 5 (fun x => (if x<2764 then (if x<2650 then (if x<2618 then (if x<1748 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2662 then (if x<2652 then 1 else 0) else (if x<2710 then 1 else (if x<2730 then 0 else 1)))) else (if x<3188 then (if x<3118 then (if x<2800 then 1 else 0) else (if x<3150 then 2 else (if x<3186 then 3 else 2))) else (if x<3288 then (if x<3256 then 3 else 2) else (if x<3298 then 3 else (if x<3300 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2661 : Finset ℕ := ([1686,1708,1714,1738,1748,1776,2618,2620,2650,2652,2662,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2661 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2661 1686 5
  · have he : independentCachedBranchMembers2661.erase 1686=independentCachedBranchMembers2659 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2659
  · have he : independentCachedBranchMembers2661.filter (independentCachedEdge 1686)=independentCachedBranchMembers2660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2660
def independentCachedBranchMembers2662 : Finset ℕ := ([1708,1738,2620,2650,2662,2702,2710,2730,2764,2792,2800,3118,3126,3180,3188,3228,3256,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2662 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2662 5 (fun x => (if x<2792 then (if x<2662 then (if x<2620 then (if x<1738 then 0 else 0) else (if x<2650 then 0 else 0)) else (if x<2710 then (if x<2702 then 1 else 0) else (if x<2730 then 1 else (if x<2764 then 1 else 1)))) else (if x<3188 then (if x<3118 then (if x<2800 then 0 else 1) else (if x<3126 then 2 else (if x<3180 then 3 else 3))) else (if x<3256 then (if x<3228 then 2 else 2) else (if x<3270 then 3 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2663 : Finset ℕ := ([1626,1686,1708,1714,1738,1748,1776,2618,2620,2650,2652,2662,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2663 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2663 1626 5
  · have he : independentCachedBranchMembers2663.erase 1626=independentCachedBranchMembers2661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2661
  · have he : independentCachedBranchMembers2663.filter (independentCachedEdge 1626)=independentCachedBranchMembers2662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2662
def independentCachedBranchMembers2664 : Finset ℕ := ([1708,1738,2620,2650,2662,2702,2710,2730,2764,2792,2800,3150,3158,3178,3186,3226,3238,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2664 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2664 5 (fun x => (if x<2792 then (if x<2662 then (if x<2620 then (if x<1738 then 0 else 0) else (if x<2650 then 0 else 0)) else (if x<2710 then (if x<2702 then 1 else 0) else (if x<2730 then 1 else (if x<2764 then 1 else 1)))) else (if x<3186 then (if x<3150 then (if x<2800 then 0 else 1) else (if x<3158 then 2 else (if x<3178 then 3 else 3))) else (if x<3238 then (if x<3226 then 2 else 2) else (if x<3288 then 2 else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2665 : Finset ℕ := ([1596,1626,1686,1708,1714,1738,1748,1776,2618,2620,2650,2652,2662,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2665 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2665 1596 5
  · have he : independentCachedBranchMembers2665.erase 1596=independentCachedBranchMembers2663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2663
  · have he : independentCachedBranchMembers2665.filter (independentCachedEdge 1596)=independentCachedBranchMembers2664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2664
def independentCachedBranchMembers2666 : Finset ℕ := ([1708,1714,1738,1748,2618,2620,2650,2652,2702,2710,2792,2800,3118,3126,3150,3158,3226,3228,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2666 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2666 5 (fun x => (if x<2792 then (if x<2620 then (if x<1738 then (if x<1714 then 0 else 0) else (if x<1748 then 0 else (if x<2618 then 0 else 1))) else (if x<2652 then (if x<2650 then 2 else 2) else (if x<2702 then 1 else (if x<2710 then 1 else 2)))) else (if x<3158 then (if x<3118 then (if x<2800 then 1 else 2) else (if x<3126 then 3 else (if x<3150 then 4 else 4))) else (if x<3228 then (if x<3226 then 3 else 3) else (if x<3298 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2667 : Finset ℕ := ([1596,1626,1686,1708,1714,1738,1748,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2667 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2667 2680 5
  · have he : independentCachedBranchMembers2667.erase 2680=independentCachedBranchMembers2665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2665
  · have he : independentCachedBranchMembers2667.filter (independentCachedEdge 2680)=independentCachedBranchMembers2666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2666
def independentCachedBranchMembers2668 : Finset ℕ := ([1686,1708,1738,1776,2618,2620,2650,2652,2662,2702,2740,2770,2792,3118,3150,3186,3188,3226,3228,3238,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2668 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2668 5 (fun x => (if x<2740 then (if x<2620 then (if x<1738 then (if x<1708 then 0 else 0) else (if x<1776 then 0 else (if x<2618 then 0 else 1))) else (if x<2652 then (if x<2650 then 2 else 2) else (if x<2662 then 1 else (if x<2702 then 1 else 0)))) else (if x<3186 then (if x<2792 then (if x<2770 then 0 else 0) else (if x<3118 then 0 else (if x<3150 then 3 else 4))) else (if x<3228 then (if x<3188 then 3 else (if x<3226 then 4 else 3)) else (if x<3238 then 4 else (if x<3270 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2669 : Finset ℕ := ([1596,1626,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2669 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2669 1768 5
  · have he : independentCachedBranchMembers2669.erase 1768=independentCachedBranchMembers2667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2667
  · have he : independentCachedBranchMembers2669.filter (independentCachedEdge 1768)=independentCachedBranchMembers2668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2668
def independentCachedBranchMembers2670 : Finset ℕ := ([1686,1708,1738,1776,2618,2620,2650,2652,2662,2702,2740,2770,2792,3126,3158,3178,3180,3256,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2670 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2670 5 (fun x => (if x<2740 then (if x<2620 then (if x<1738 then (if x<1708 then 0 else 0) else (if x<1776 then 0 else (if x<2618 then 0 else 1))) else (if x<2652 then (if x<2650 then 2 else 2) else (if x<2662 then 1 else (if x<2702 then 1 else 0)))) else (if x<3178 then (if x<2792 then (if x<2770 then 0 else 0) else (if x<3126 then 0 else (if x<3158 then 3 else 4))) else (if x<3288 then (if x<3180 then 3 else (if x<3256 then 4 else 3)) else (if x<3298 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2671 : Finset ℕ := ([1596,1626,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2671 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2671 1678 5
  · have he : independentCachedBranchMembers2671.erase 1678=independentCachedBranchMembers2669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2669
  · have he : independentCachedBranchMembers2671.filter (independentCachedEdge 1678)=independentCachedBranchMembers2670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2670
def independentCachedBranchMembers2672 : Finset ℕ := ([1596,1626,1714,1748,2618,2652,2662,2702,2710,2740,2770,2792,2800,3118,3126,3178,3186,3226,3256,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2672 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2672 5 (fun x => (if x<2770 then (if x<2652 then (if x<1714 then (if x<1626 then 0 else 0) else (if x<1748 then 0 else (if x<2618 then 0 else 0))) else (if x<2702 then (if x<2662 then 0 else 1) else (if x<2710 then 1 else (if x<2740 then 2 else 0)))) else (if x<3178 then (if x<2800 then (if x<2792 then 0 else 1) else (if x<3118 then 2 else (if x<3126 then 3 else 4))) else (if x<3256 then (if x<3186 then 4 else (if x<3226 then 3 else 3)) else (if x<3270 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2673 : Finset ℕ := ([1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2673 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2673 1628 5
  · have he : independentCachedBranchMembers2673.erase 1628=independentCachedBranchMembers2671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2671
  · have he : independentCachedBranchMembers2673.filter (independentCachedEdge 1628)=independentCachedBranchMembers2672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2672
def independentCachedBranchMembers2674 : Finset ℕ := ([1596,1626,1714,1748,2618,2652,2662,2702,2710,2740,2770,2792,2800,3150,3158,3180,3188,3228,3238,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2674 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2674 5 (fun x => (if x<2770 then (if x<2652 then (if x<1714 then (if x<1626 then 0 else 0) else (if x<1748 then 0 else (if x<2618 then 0 else 0))) else (if x<2702 then (if x<2662 then 0 else 1) else (if x<2710 then 1 else (if x<2740 then 2 else 0)))) else (if x<3180 then (if x<2800 then (if x<2792 then 0 else 1) else (if x<3150 then 2 else (if x<3158 then 3 else 4))) else (if x<3238 then (if x<3188 then 4 else (if x<3228 then 3 else 3)) else (if x<3288 then 3 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2675 : Finset ℕ := ([1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2675 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2675 1594 5
  · have he : independentCachedBranchMembers2675.erase 1594=independentCachedBranchMembers2673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2673
  · have he : independentCachedBranchMembers2675.filter (independentCachedEdge 1594)=independentCachedBranchMembers2674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2674
def independentCachedBranchMembers2676 : Finset ℕ := ([1594,1626,1678,1686,1714,1738,2618,2650,2662,2702,2710,2730,2770,3118,3126,3150,3158,3178,3186,3226,3238,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2676 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2676 5 (fun x => (if x<2730 then (if x<1738 then (if x<1678 then (if x<1626 then 0 else 1) else (if x<1686 then 0 else (if x<1714 then 1 else 2))) else (if x<2662 then (if x<2618 then 2 else (if x<2650 then 3 else 4)) else (if x<2702 then 3 else (if x<2710 then 3 else 4)))) else (if x<3178 then (if x<3126 then (if x<2770 then 0 else (if x<3118 then 1 else 0)) else (if x<3150 then 2 else (if x<3158 then 2 else 1))) else (if x<3238 then (if x<3186 then 4 else (if x<3226 then 3 else 0)) else (if x<3270 then 4 else (if x<3298 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2677 : Finset ℕ := ([252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2677 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2677 252 5
  · have he : independentCachedBranchMembers2677.erase 252=independentCachedBranchMembers2675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2675
  · have he : independentCachedBranchMembers2677.filter (independentCachedEdge 252)=independentCachedBranchMembers2676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2676
def independentCachedBranchMembers2678 : Finset ℕ := ([1596,1628,1714,1738,1768,1776,2620,2652,2662,2730,2770,2792,2800,3118,3126,3150,3158,3180,3188,3226,3256,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2678 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2678 5 (fun x => (if x<2792 then (if x<1776 then (if x<1714 then (if x<1628 then 0 else 1) else (if x<1738 then 0 else (if x<1768 then 1 else 0))) else (if x<2662 then (if x<2620 then 1 else (if x<2652 then 2 else 3)) else (if x<2730 then 2 else (if x<2770 then 2 else 3)))) else (if x<3180 then (if x<3126 then (if x<2800 then 3 else (if x<3118 then 2 else 2)) else (if x<3150 then 0 else (if x<3158 then 1 else 3))) else (if x<3256 then (if x<3188 then 0 else (if x<3226 then 1 else 4)) else (if x<3288 then 0 else (if x<3298 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2679 : Finset ℕ := ([132,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2679 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2679 132 5
  · have he : independentCachedBranchMembers2679.erase 132=independentCachedBranchMembers2677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2677
  · have he : independentCachedBranchMembers2679.filter (independentCachedEdge 132)=independentCachedBranchMembers2678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2678
def independentCachedBranchMembers2680 : Finset ℕ := ([1594,1596,1678,1708,1748,1776,2618,2620,2662,2702,2730,2770,2800,3118,3158,3186,3188,3226,3228,3256,3270,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2680 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2680 5 (fun x => (if x<2770 then (if x<1776 then (if x<1678 then (if x<1596 then 0 else 1) else (if x<1708 then 0 else (if x<1748 then 2 else 1))) else (if x<2662 then (if x<2618 then 2 else (if x<2620 then 1 else 3)) else (if x<2702 then 3 else (if x<2730 then 2 else 0)))) else (if x<3226 then (if x<3158 then (if x<2800 then 1 else (if x<3118 then 3 else 0)) else (if x<3186 then 4 else (if x<3188 then 2 else 3))) else (if x<3270 then (if x<3228 then 0 else (if x<3256 then 4 else 3)) else (if x<3298 then 1 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2681 : Finset ℕ := ([72,132,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2681 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2681 72 5
  · have he : independentCachedBranchMembers2681.erase 72=independentCachedBranchMembers2679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2679
  · have he : independentCachedBranchMembers2681.filter (independentCachedEdge 72)=independentCachedBranchMembers2680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2680
def independentCachedBranchMembers2682 : Finset ℕ := ([1626,1628,1686,1708,1748,1768,2650,2652,2662,2710,2730,2770,2792,3118,3158,3178,3180,3226,3228,3238,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2682 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2682 5 (fun x => (if x<2770 then (if x<1768 then (if x<1686 then (if x<1628 then 0 else 1) else (if x<1708 then 0 else (if x<1748 then 1 else 2))) else (if x<2662 then (if x<2650 then 2 else (if x<2652 then 1 else 3)) else (if x<2710 then 3 else (if x<2730 then 2 else 1)))) else (if x<3226 then (if x<3158 then (if x<2792 then 0 else (if x<3118 then 3 else 4)) else (if x<3178 then 0 else (if x<3180 then 2 else 3))) else (if x<3288 then (if x<3228 then 0 else (if x<3238 then 4 else 1)) else (if x<3298 then 3 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2683 : Finset ℕ := ([48,72,132,252,1594,1596,1626,1628,1678,1686,1708,1714,1738,1748,1768,1776,2618,2620,2650,2652,2662,2680,2702,2710,2730,2740,2764,2770,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2683 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2683 48 5
  · have he : independentCachedBranchMembers2683.erase 48=independentCachedBranchMembers2681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2681
  · have he : independentCachedBranchMembers2683.filter (independentCachedEdge 48)=independentCachedBranchMembers2682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2682
def independentCachedBranchMembers2684 : Finset ℕ := ([132,252,1628,1686,1708,1748,2620,2652,2662,2702,2710,2740,2764,3118,3126,3150,3158,3180,3188,3228,3238,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2684 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2684 5 (fun x => (if x<2740 then (if x<1748 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1686 then 1 else (if x<1708 then 1 else 0))) else (if x<2662 then (if x<2620 then 0 else (if x<2652 then 2 else 3)) else (if x<2702 then 2 else (if x<2710 then 2 else 3)))) else (if x<3180 then (if x<3126 then (if x<2764 then 0 else (if x<3118 then 0 else 2)) else (if x<3150 then 4 else (if x<3158 then 4 else 1))) else (if x<3238 then (if x<3188 then 1 else (if x<3228 then 2 else 0)) else (if x<3270 then 1 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2685 : Finset ℕ := ([252,1686,1708,2620,2652,2662,2702,2740,3126,3158,3180,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2685 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2685 4 (fun x => (if x<2702 then (if x<2620 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<2652 then 0 else (if x<2662 then 2 else 2))) else (if x<3158 then (if x<2740 then 1 else (if x<3126 then 1 else 3)) else (if x<3180 then 2 else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2686 : Finset ℕ := ([132,252,1628,1678,1686,1708,1748,2620,2652,2662,2702,2710,2740,2764,3118,3126,3150,3158,3180,3188,3228,3238,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2686 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2686 1678 4
  · have he : independentCachedBranchMembers2686.erase 1678=independentCachedBranchMembers2684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2684
  · have he : independentCachedBranchMembers2686.filter (independentCachedEdge 1678)=independentCachedBranchMembers2685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2685
def independentCachedBranchMembers2687 : Finset ℕ := ([132,1628,1708,2620,2662,2702,2710,2764,3150,3158,3238,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2687 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2687 4 (fun x => (if x<2710 then (if x<2620 then (if x<1628 then 0 else (if x<1708 then 1 else 0)) else (if x<2662 then 1 else (if x<2702 then 2 else 0))) else (if x<3158 then (if x<2764 then 2 else (if x<3150 then 1 else 3)) else (if x<3238 then 2 else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
