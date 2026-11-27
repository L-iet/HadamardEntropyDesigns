/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch89
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5664 : Finset ℕ := ([40,80,130,144,246,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5664 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5664 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5664 144 4
  · have he : independentCachedBranchMembers5664.erase 144=independentCachedBranchMembers5662 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5662
  · have he : independentCachedBranchMembers5664.filter (independentCachedEdge 144)=independentCachedBranchMembers5663 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5663
def independentCachedBranchMembers5665 : Finset ℕ := ([80,130,1644,1714,1748,1752,2606,2710,2714,2800,3102,3188,3192,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5665 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5665 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5665 4 (fun x => (if x<2714 then (if x<1748 then (if x<1644 then (if x<130 then 0 else 0) else (if x<1714 then 1 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2710 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2800 then 2 else 2) else (if x<3188 then 3 else 0)) else (if x<3242 then (if x<3238 then 3 else 0) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5666 : Finset ℕ := ([40,66,80,130,144,246,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5666 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5666 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5666 66 4
  · have he : independentCachedBranchMembers5666.erase 66=independentCachedBranchMembers5664 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5664
  · have he : independentCachedBranchMembers5666.filter (independentCachedEdge 66)=independentCachedBranchMembers5665 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5665
def independentCachedBranchMembers5667 : Finset ℕ := ([40,250,1650,1714,1734,1748,2646,2710,2786,2800,3102,3178,3192,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5667 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5667 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5667 4 (fun x => (if x<2786 then (if x<1734 then (if x<1650 then (if x<250 then 0 else 0) else (if x<1714 then 1 else 2)) else (if x<2646 then (if x<1748 then 1 else 2) else (if x<2710 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2800 then 1 else 2) else (if x<3178 then 3 else 0)) else (if x<3256 then (if x<3242 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5668 : Finset ℕ := ([36,40,66,80,130,144,246,250,1644,1650,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2710,2714,2786,2800,3072,3102,3174,3178,3188,3192,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5668 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5668 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5668 36 4
  · have he : independentCachedBranchMembers5668.erase 36=independentCachedBranchMembers5666 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5666
  · have he : independentCachedBranchMembers5668.filter (independentCachedEdge 36)=independentCachedBranchMembers5667 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5667
def independentCachedBranchMembers5669 : Finset ℕ := ([34,36,40,48,66,68,72,80,130,132,136,144,238,246,250,252,1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2702,2710,2714,2716,2786,2788,2792,2800,3072,3102,3174,3178,3180,3186,3188,3192,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5669 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5669 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5669 1740 5
  · have he : independentCachedBranchMembers5669.erase 1740=independentCachedBranchMembers5649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5649
  · have he : independentCachedBranchMembers5669.filter (independentCachedEdge 1740)=independentCachedBranchMembers5668 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5668
def independentCachedBranchMembers5670 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5670 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5670 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5670 2590 6
  · have he : independentCachedBranchMembers5670.erase 2590=independentCachedBranchMembers5492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5492
  · have he : independentCachedBranchMembers5670.filter (independentCachedEdge 2590)=independentCachedBranchMembers5669 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5669
def independentCachedBranchMembers5671 : Finset ℕ := ([1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3276,3282,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5671 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5671 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5671 6 (fun x => (if x<3158 then (if x<1738 then (if x<1708 then (if x<1652 then (if x<1650 then 0 else 0) else (if x<1702 then 1 else 0)) else (if x<1720 then (if x<1714 then 1 else 1) else (if x<1734 then 0 else 1))) else (if x<3118 then (if x<1752 then (if x<1748 then 0 else 0) else (if x<3072 then 1 else 2)) else (if x<3130 then (if x<3126 then 2 else 3) else (if x<3132 then 4 else (if x<3150 then 5 else 3))))) else (if x<3228 then (if x<3192 then (if x<3164 then (if x<3162 then 2 else 5) else (if x<3174 then 4 else 4)) else (if x<3222 then (if x<3214 then 2 else 4) else (if x<3226 then 5 else 2))) else (if x<3282 then (if x<3252 then (if x<3242 then 3 else 3) else (if x<3276 then 2 else 2)) else (if x<3300 then (if x<3298 then 3 else 2) else (if x<3304 then 3 else (if x<3312 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5672 : Finset ℕ := ([1644,1650,1738,1748,3072,3126,3132,3158,3164,3214,3226,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5672 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5672 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5672 5 (fun x => (if x<3158 then (if x<1748 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<3126 then (if x<3072 then 0 else 1) else (if x<3132 then 1 else 2))) else (if x<3276 then (if x<3214 then (if x<3164 then 2 else 1) else (if x<3226 then 1 else 2)) else (if x<3300 then (if x<3282 then 0 else 0) else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5673 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3276,3282,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5673 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5673 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5673 1642 5
  · have he : independentCachedBranchMembers5673.erase 1642=independentCachedBranchMembers5671 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5671
  · have he : independentCachedBranchMembers5673.filter (independentCachedEdge 1642)=independentCachedBranchMembers5672 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5672
def independentCachedBranchMembers5674 : Finset ℕ := ([1644,1650,1702,1708,1714,1720,1738,1748,3118,3130,3158,3164,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5674 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5674 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5674 5 (fun x => (if x<3158 then (if x<1720 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1708 then 0 else (if x<1714 then 1 else 1))) else (if x<1748 then (if x<1738 then 0 else 0) else (if x<3118 then 0 else (if x<3130 then 2 else 3)))) else (if x<3252 then (if x<3222 then (if x<3164 then 2 else 3) else (if x<3228 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3300 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5675 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5675 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5675 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5675 3284 5
  · have he : independentCachedBranchMembers5675.erase 3284=independentCachedBranchMembers5673 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5673
  · have he : independentCachedBranchMembers5675.filter (independentCachedEdge 3284)=independentCachedBranchMembers5674 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5674
def independentCachedBranchMembers5676 : Finset ℕ := ([1644,1650,1702,1708,1714,1720,1738,1748,3126,3132,3150,3162,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5676 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5676 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5676 5 (fun x => (if x<3150 then (if x<1720 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1708 then 0 else (if x<1714 then 1 else 1))) else (if x<1748 then (if x<1738 then 0 else 0) else (if x<3126 then 0 else (if x<3132 then 2 else 3)))) else (if x<3252 then (if x<3214 then (if x<3162 then 2 else 3) else (if x<3226 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3298 then 1 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5677 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3252,3274,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5677 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5677 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5677 3274 5
  · have he : independentCachedBranchMembers5677.erase 3274=independentCachedBranchMembers5675 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5675
  · have he : independentCachedBranchMembers5677.filter (independentCachedEdge 3274)=independentCachedBranchMembers5676 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5676
def independentCachedBranchMembers5678 : Finset ℕ := ([1642,1652,1708,1714,1734,1738,1748,1752,3126,3130,3150,3164,3222,3226,3242,3252,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5678 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5678 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5678 5 (fun x => (if x<3150 then (if x<1738 then (if x<1708 then (if x<1652 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 0 else 0))) else (if x<1752 then (if x<1748 then 1 else 1) else (if x<3126 then 0 else (if x<3130 then 2 else 3)))) else (if x<3252 then (if x<3222 then (if x<3164 then 2 else 3) else (if x<3226 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3298 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5679 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3250,3252,3274,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5679 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5679 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5679 3250 5
  · have he : independentCachedBranchMembers5679.erase 3250=independentCachedBranchMembers5677 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5677
  · have he : independentCachedBranchMembers5679.filter (independentCachedEdge 3250)=independentCachedBranchMembers5678 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5678
def independentCachedBranchMembers5680 : Finset ℕ := ([1642,1652,1708,1714,1734,1738,1748,1752,3118,3132,3158,3162,3214,3228,3242,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5680 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5680 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5680 5 (fun x => (if x<3158 then (if x<1738 then (if x<1708 then (if x<1652 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 0 else 0))) else (if x<1752 then (if x<1748 then 1 else 1) else (if x<3118 then 0 else (if x<3132 then 2 else 3)))) else (if x<3252 then (if x<3214 then (if x<3162 then 2 else 3) else (if x<3228 then 3 else (if x<3242 then 2 else 1))) else (if x<3282 then (if x<3276 then 1 else 1) else (if x<3300 then 1 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5681 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5681 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5681 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5681 3244 5
  · have he : independentCachedBranchMembers5681.erase 3244=independentCachedBranchMembers5679 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5679
  · have he : independentCachedBranchMembers5681.filter (independentCachedEdge 3244)=independentCachedBranchMembers5680 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5680
def independentCachedBranchMembers5682 : Finset ℕ := ([1642,1644,1650,1652,1708,1714,1734,1752,3118,3126,3162,3164,3174,3192,3226,3228,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5682 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5682 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5682 5 (fun x => (if x<3164 then (if x<1714 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else (if x<1708 then 0 else 0))) else (if x<3118 then (if x<1734 then 0 else (if x<1752 then 0 else 0)) else (if x<3126 then 2 else (if x<3162 then 3 else 2)))) else (if x<3274 then (if x<3192 then (if x<3174 then 3 else 1) else (if x<3226 then 1 else (if x<3228 then 3 else 2))) else (if x<3284 then (if x<3276 then 4 else (if x<3282 then 1 else 1)) else (if x<3304 then 4 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5683 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5683 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5683 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5683 3288 5
  · have he : independentCachedBranchMembers5683.erase 3288=independentCachedBranchMembers5681 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5681
  · have he : independentCachedBranchMembers5683.filter (independentCachedEdge 3288)=independentCachedBranchMembers5682 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5682
def independentCachedBranchMembers5684 : Finset ℕ := ([1642,1644,1650,1652,1708,1714,1734,1752,3130,3132,3150,3158,3174,3192,3214,3222,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5684 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5684 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5684 5 (fun x => (if x<3158 then (if x<1714 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else (if x<1708 then 0 else 0))) else (if x<3130 then (if x<1734 then 0 else (if x<1752 then 0 else 0)) else (if x<3132 then 2 else (if x<3150 then 3 else 2)))) else (if x<3274 then (if x<3192 then (if x<3174 then 3 else 1) else (if x<3214 then 1 else (if x<3222 then 3 else 2))) else (if x<3284 then (if x<3276 then 4 else (if x<3282 then 1 else 1)) else (if x<3298 then 4 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5685 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3192,3214,3222,3226,3228,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5685 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5685 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5685 3270 5
  · have he : independentCachedBranchMembers5685.erase 3270=independentCachedBranchMembers5683 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5683
  · have he : independentCachedBranchMembers5685.filter (independentCachedEdge 3270)=independentCachedBranchMembers5684 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5684
def independentCachedBranchMembers5686 : Finset ℕ := ([1644,1650,1702,1720,1734,1738,1748,1752,3126,3130,3158,3162,3174,3192,3214,3228,3244,3250,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5686 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5686 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5686 5 (fun x => (if x<3162 then (if x<1738 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1734 then 0 else 1))) else (if x<3126 then (if x<1748 then 0 else (if x<1752 then 0 else 1)) else (if x<3130 then 2 else (if x<3158 then 3 else 3)))) else (if x<3244 then (if x<3192 then (if x<3174 then 2 else 1) else (if x<3214 then 1 else (if x<3228 then 2 else 3))) else (if x<3282 then (if x<3250 then 4 else (if x<3276 then 4 else 1)) else (if x<3298 then 1 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5687 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3186,3192,3214,3222,3226,3228,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5687 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5687 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5687 3186 5
  · have he : independentCachedBranchMembers5687.erase 3186=independentCachedBranchMembers5685 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5685
  · have he : independentCachedBranchMembers5687.filter (independentCachedEdge 3186)=independentCachedBranchMembers5686 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5686
def independentCachedBranchMembers5688 : Finset ℕ := ([1644,1650,1702,1720,1734,1738,1748,1752,3118,3132,3150,3164,3174,3192,3222,3226,3244,3250,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5688 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5688 5 (fun x => (if x<3164 then (if x<1738 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1720 then 0 else (if x<1734 then 0 else 1))) else (if x<3118 then (if x<1748 then 0 else (if x<1752 then 0 else 1)) else (if x<3132 then 2 else (if x<3150 then 3 else 3)))) else (if x<3244 then (if x<3192 then (if x<3174 then 2 else 1) else (if x<3222 then 1 else (if x<3226 then 2 else 3))) else (if x<3282 then (if x<3250 then 4 else (if x<3276 then 4 else 1)) else (if x<3300 then 1 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5689 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3192,3214,3222,3226,3228,3242,3244,3250,3252,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5689 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5689 3180 5
  · have he : independentCachedBranchMembers5689.erase 3180=independentCachedBranchMembers5687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5687
  · have he : independentCachedBranchMembers5689.filter (independentCachedEdge 3180)=independentCachedBranchMembers5688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5688
def independentCachedBranchMembers5690 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1738,1748,3130,3132,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3270,3288,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5690 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5690 5 (fun x => (if x<3174 then (if x<1738 then (if x<1652 then (if x<1644 then 0 else (if x<1650 then 1 else 1)) else (if x<1702 then 0 else (if x<1720 then 0 else 0))) else (if x<3132 then (if x<1748 then 1 else (if x<3130 then 1 else 2)) else (if x<3150 then 3 else (if x<3158 then 2 else 3)))) else (if x<3250 then (if x<3228 then (if x<3192 then 0 else (if x<3226 then 0 else 3)) else (if x<3242 then 2 else (if x<3244 then 0 else 4))) else (if x<3288 then (if x<3252 then 4 else (if x<3270 then 0 else 4)) else (if x<3304 then 4 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5691 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3192,3214,3222,3226,3228,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5691 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5691 3256 5
  · have he : independentCachedBranchMembers5691.erase 3256=independentCachedBranchMembers5689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5689
  · have he : independentCachedBranchMembers5691.filter (independentCachedEdge 3256)=independentCachedBranchMembers5690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5690
def independentCachedBranchMembers5692 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1738,1748,3118,3126,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3270,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5692 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5692 5 (fun x => (if x<3174 then (if x<1738 then (if x<1652 then (if x<1644 then 0 else (if x<1650 then 1 else 1)) else (if x<1702 then 0 else (if x<1720 then 0 else 0))) else (if x<3126 then (if x<1748 then 1 else (if x<3118 then 1 else 2)) else (if x<3162 then 3 else (if x<3164 then 2 else 3)))) else (if x<3250 then (if x<3222 then (if x<3192 then 0 else (if x<3214 then 0 else 3)) else (if x<3242 then 2 else (if x<3244 then 0 else 4))) else (if x<3288 then (if x<3252 then 4 else (if x<3270 then 0 else 4)) else (if x<3298 then 4 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5693 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5693 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5693 3238 5
  · have he : independentCachedBranchMembers5693.erase 3238=independentCachedBranchMembers5691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5691
  · have he : independentCachedBranchMembers5693.filter (independentCachedEdge 3238)=independentCachedBranchMembers5692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5692
def independentCachedBranchMembers5694 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1734,1752,3126,3132,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3274,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5694 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5694 5 (fun x => (if x<3174 then (if x<1734 then (if x<1708 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<1714 then 1 else (if x<1720 then 1 else 0))) else (if x<3132 then (if x<1752 then 1 else (if x<3126 then 1 else 2)) else (if x<3158 then 3 else (if x<3164 then 3 else 2)))) else (if x<3242 then (if x<3192 then (if x<3180 then 0 else (if x<3186 then 4 else 4)) else (if x<3214 then 0 else (if x<3226 then 2 else 3))) else (if x<3284 then (if x<3252 then 0 else (if x<3274 then 0 else 4)) else (if x<3300 then 4 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5695 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5695 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5695 3188 5
  · have he : independentCachedBranchMembers5695.erase 3188=independentCachedBranchMembers5693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5693
  · have he : independentCachedBranchMembers5695.filter (independentCachedEdge 3188)=independentCachedBranchMembers5694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5694
end EntropyDesigns.QuadraticRefinement
