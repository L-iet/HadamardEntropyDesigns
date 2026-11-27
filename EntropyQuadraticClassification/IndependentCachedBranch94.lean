/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch93
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5792 : Finset ℕ := ([1596,1628,1642,1650,1678,1686,1708,1720,1748,1752,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5792 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5792 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5792 3300 4
  · have he : independentCachedBranchMembers5792.erase 3300=independentCachedBranchMembers5790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5790
  · have he : independentCachedBranchMembers5792.filter (independentCachedEdge 3300)=independentCachedBranchMembers5791 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5791
def independentCachedBranchMembers5793 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1748,1752,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5793 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5793 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5793 1692 5
  · have he : independentCachedBranchMembers5793.erase 1692=independentCachedBranchMembers5781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5781
  · have he : independentCachedBranchMembers5793.filter (independentCachedEdge 1692)=independentCachedBranchMembers5792 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5792
def independentCachedBranchMembers5794 : Finset ℕ := ([1626,1628,1642,1644,1678,1720,1734,1776,3072,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5794 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5794 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5794 5 (fun x => (if x<3188 then (if x<1734 then (if x<1644 then (if x<1628 then 0 else (if x<1642 then 1 else 1)) else (if x<1678 then 0 else (if x<1720 then 0 else 0))) else (if x<3130 then (if x<1776 then 1 else (if x<3072 then 1 else 2)) else (if x<3150 then (if x<3132 then 2 else 3) else (if x<3186 then 0 else 3)))) else (if x<3244 then (if x<3226 then (if x<3192 then 2 else (if x<3222 then 0 else 2)) else (if x<3238 then (if x<3228 then 0 else 4) else (if x<3242 then 3 else 4))) else (if x<3288 then (if x<3282 then 0 else (if x<3284 then 4 else 1)) else (if x<3300 then (if x<3298 then 2 else 1) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5795 : Finset ℕ := ([1626,1642,1678,1734,3072,3130,3186,3192,3222,3228,3238,3244,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5795 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5795 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5795 4 (fun x => (if x<3192 then (if x<1734 then (if x<1642 then 0 else (if x<1678 then 1 else 0)) else (if x<3130 then (if x<3072 then 1 else 2) else (if x<3186 then 1 else 0))) else (if x<3238 then (if x<3222 then 2 else (if x<3228 then 1 else 2)) else (if x<3284 then (if x<3244 then 0 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5796 : Finset ℕ := ([1626,1628,1642,1644,1678,1720,1734,1738,1776,3072,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5796 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5796 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5796 1738 4
  · have he : independentCachedBranchMembers5796.erase 1738=independentCachedBranchMembers5794 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5794
  · have he : independentCachedBranchMembers5796.filter (independentCachedEdge 1738)=independentCachedBranchMembers5795 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5795
def independentCachedBranchMembers5797 : Finset ℕ := ([1628,1644,1720,1776,3072,3132,3188,3192,3228,3244,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5797 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5797 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5797 4 (fun x => (if x<3192 then (if x<1776 then (if x<1644 then 0 else (if x<1720 then 1 else 0)) else (if x<3132 then (if x<3072 then 1 else 2) else (if x<3188 then 0 else 1))) else (if x<3284 then (if x<3228 then 2 else (if x<3244 then 2 else 3)) else (if x<3300 then (if x<3288 then 3 else 0) else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5798 : Finset ℕ := ([1626,1628,1642,1644,1678,1714,1720,1734,1738,1776,3072,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5798 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5798 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5798 1714 4
  · have he : independentCachedBranchMembers5798.erase 1714=independentCachedBranchMembers5796 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5796
  · have he : independentCachedBranchMembers5798.filter (independentCachedEdge 1714)=independentCachedBranchMembers5797 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5797
def independentCachedBranchMembers5799 : Finset ℕ := ([1626,1628,1642,1644,1678,1720,1734,1776,3130,3132,3186,3188,3222,3238,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5799 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5799 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5799 4 (fun x => (if x<3130 then (if x<1678 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1644 then 1 else 0)) else (if x<1734 then (if x<1720 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3222 then (if x<3186 then (if x<3132 then 2 else 3) else (if x<3188 then 3 else 2)) else (if x<3288 then (if x<3238 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5800 : Finset ℕ := ([1626,1628,1642,1644,1678,1714,1720,1734,1738,1776,3072,3126,3130,3132,3150,3186,3188,3192,3222,3226,3228,3238,3242,3244,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5800 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5800 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5800 3126 4
  · have he : independentCachedBranchMembers5800.erase 3126=independentCachedBranchMembers5798 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5798
  · have he : independentCachedBranchMembers5800.filter (independentCachedEdge 3126)=independentCachedBranchMembers5799 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5799
def independentCachedBranchMembers5801 : Finset ℕ := ([1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1748,1752,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5801 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5801 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5801 1614 5
  · have he : independentCachedBranchMembers5801.erase 1614=independentCachedBranchMembers5793 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5793
  · have he : independentCachedBranchMembers5801.filter (independentCachedEdge 1614)=independentCachedBranchMembers5800 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5800
def independentCachedBranchMembers5802 : Finset ℕ := ([1594,1596,1650,1652,1686,1702,1738,1752,1768,3072,3126,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5802 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5802 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5802 5 (fun x => (if x<3180 then (if x<1752 then (if x<1652 then (if x<1596 then 0 else (if x<1650 then 1 else 1)) else (if x<1702 then (if x<1686 then 0 else 0) else (if x<1738 then 1 else 2))) else (if x<3126 then (if x<1768 then 0 else (if x<3072 then 1 else 3)) else (if x<3164 then (if x<3162 then 0 else 2) else (if x<3178 then 3 else 3)))) else (if x<3256 then (if x<3226 then (if x<3192 then 4 else (if x<3214 then 0 else 2)) else (if x<3242 then (if x<3228 then 0 else 4) else (if x<3244 then 4 else 1))) else (if x<3284 then (if x<3270 then 3 else (if x<3282 then 4 else 3)) else (if x<3300 then (if x<3298 then 0 else 1) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5803 : Finset ℕ := ([1594,1650,1686,1702,3072,3162,3178,3192,3214,3228,3244,3270,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5803 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5803 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5803 4 (fun x => (if x<3192 then (if x<1702 then (if x<1650 then 0 else (if x<1686 then 1 else 0)) else (if x<3162 then (if x<3072 then 1 else 2) else (if x<3178 then 1 else 0))) else (if x<3244 then (if x<3214 then 2 else (if x<3228 then 1 else 2)) else (if x<3284 then (if x<3270 then 3 else 0) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5804 : Finset ℕ := ([1594,1596,1650,1652,1686,1702,1714,1738,1752,1768,3072,3126,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5804 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5804 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5804 1714 4
  · have he : independentCachedBranchMembers5804.erase 1714=independentCachedBranchMembers5802 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5802
  · have he : independentCachedBranchMembers5804.filter (independentCachedEdge 1714)=independentCachedBranchMembers5803 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5803
def independentCachedBranchMembers5805 : Finset ℕ := ([1594,1596,1650,1652,1686,1702,1752,1768,3162,3164,3178,3180,3214,3256,3270,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5805 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5805 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5805 4 (fun x => (if x<3162 then (if x<1686 then (if x<1650 then (if x<1596 then 0 else 1) else (if x<1652 then 1 else 0)) else (if x<1752 then (if x<1702 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<3214 then (if x<3178 then (if x<3164 then 2 else 3) else (if x<3180 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5806 : Finset ℕ := ([1594,1596,1650,1652,1686,1702,1714,1738,1752,1768,3072,3126,3150,3162,3164,3178,3180,3192,3214,3226,3228,3242,3244,3256,3270,3282,3284,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5806 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5806 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5806 3150 4
  · have he : independentCachedBranchMembers5806.erase 3150=independentCachedBranchMembers5804 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5804
  · have he : independentCachedBranchMembers5806.filter (independentCachedEdge 3150)=independentCachedBranchMembers5805 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5805
def independentCachedBranchMembers5807 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1748,1752,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5807 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5807 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5807 1590 5
  · have he : independentCachedBranchMembers5807.erase 1590=independentCachedBranchMembers5801 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5801
  · have he : independentCachedBranchMembers5807.filter (independentCachedEdge 1590)=independentCachedBranchMembers5806 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5806
def independentCachedBranchMembers5808 : Finset ℕ := ([1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,3072,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5808 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5808 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5808 5 (fun x => (if x<3150 then (if x<1738 then (if x<1692 then (if x<1642 then 0 else (if x<1650 then 0 else 1)) else (if x<1714 then (if x<1702 then 2 else 1) else (if x<1734 then 2 else 0))) else (if x<1776 then (if x<1764 then 1 else (if x<1768 then 2 else 3)) else (if x<3126 then (if x<3072 then 0 else 4) else (if x<3130 then 1 else 4)))) else (if x<3244 then (if x<3188 then (if x<3162 then 0 else (if x<3180 then 1 else 3)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3222 then 1 else 4))) else (if x<3276 then (if x<3252 then 4 else (if x<3256 then 2 else 3)) else (if x<3288 then (if x<3284 then 2 else 0) else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5809 : Finset ℕ := ([1628,1692,1734,1738,3072,3150,3162,3214,3222,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5809 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5809 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5809 4 (fun x => (if x<3162 then (if x<1738 then (if x<1692 then 0 else (if x<1734 then 1 else 0)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3276 then (if x<3214 then 2 else (if x<3222 then 1 else 2)) else (if x<3284 then 2 else (if x<3288 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5810 : Finset ℕ := ([1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,3072,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5810 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5810 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5810 1596 4
  · have he : independentCachedBranchMembers5810.erase 1596=independentCachedBranchMembers5808 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5808
  · have he : independentCachedBranchMembers5810.filter (independentCachedEdge 1596)=independentCachedBranchMembers5809 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5809
def independentCachedBranchMembers5811 : Finset ℕ := ([1596,1628,1642,1650,1702,1734,1768,1776,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5811 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5811 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5811 4 (fun x => (if x<3130 then (if x<1702 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1650 then 0 else 1)) else (if x<1768 then (if x<1734 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3214 then (if x<3180 then (if x<3162 then 2 else 3) else (if x<3188 then 2 else 3)) else (if x<3256 then (if x<3222 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5812 : Finset ℕ := ([1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,3072,3126,3130,3150,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5812 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5812 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5812 3226 4
  · have he : independentCachedBranchMembers5812.erase 3226=independentCachedBranchMembers5810 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5810
  · have he : independentCachedBranchMembers5812.filter (independentCachedEdge 3226)=independentCachedBranchMembers5811 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5811
def independentCachedBranchMembers5813 : Finset ℕ := ([1596,1642,1692,1702,1714,1738,1764,1776,3126,3150,3162,3188,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5813 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5813 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5813 4 (fun x => (if x<3126 then (if x<1714 then (if x<1692 then (if x<1642 then 0 else 0) else (if x<1702 then 1 else 0)) else (if x<1764 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3222 then (if x<3162 then (if x<3150 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3244 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5814 : Finset ℕ := ([1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,3072,3126,3130,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5814 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5814 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5814 3158 4
  · have he : independentCachedBranchMembers5814.erase 3158=independentCachedBranchMembers5812 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5812
  · have he : independentCachedBranchMembers5814.filter (independentCachedEdge 3158)=independentCachedBranchMembers5813 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5813
def independentCachedBranchMembers5815 : Finset ℕ := ([1628,1650,1692,1714,1734,1738,1764,1768,3126,3130,3150,3180,3214,3244,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5815 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5815 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5815 4 (fun x => (if x<3126 then (if x<1734 then (if x<1692 then (if x<1650 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1764 then (if x<1738 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3214 then (if x<3150 then (if x<3130 then 2 else 3) else (if x<3180 then 2 else 3)) else (if x<3284 then (if x<3244 then 3 else 2) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5816 : Finset ℕ := ([1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5816 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5816 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5816 3118 4
  · have he : independentCachedBranchMembers5816.erase 3118=independentCachedBranchMembers5814 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5814
  · have he : independentCachedBranchMembers5816.filter (independentCachedEdge 3118)=independentCachedBranchMembers5815 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5815
def independentCachedBranchMembers5817 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1748,1752,1762,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5817 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5817 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5817 1762 5
  · have he : independentCachedBranchMembers5817.erase 1762=independentCachedBranchMembers5807 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5807
  · have he : independentCachedBranchMembers5817.filter (independentCachedEdge 1762)=independentCachedBranchMembers5816 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5816
def independentCachedBranchMembers5818 : Finset ℕ := ([1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,3072,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5818 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5818 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5818 5 (fun x => (if x<3150 then (if x<1720 then (if x<1678 then (if x<1644 then 0 else (if x<1652 then 0 else 1)) else (if x<1692 then (if x<1686 then 0 else 1) else (if x<1714 then 2 else 2))) else (if x<1764 then (if x<1738 then 0 else (if x<1752 then 2 else 1)) else (if x<3126 then (if x<3072 then 2 else 3) else (if x<3132 then 1 else 3)))) else (if x<3244 then (if x<3186 then (if x<3164 then 0 else (if x<3178 then 4 else 3)) else (if x<3226 then (if x<3192 then 4 else 0) else (if x<3238 then 0 else 3))) else (if x<3276 then (if x<3252 then 0 else (if x<3270 then 2 else 4)) else (if x<3304 then (if x<3284 then 2 else 1) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5819 : Finset ℕ := ([1626,1714,1720,1764,3072,3150,3164,3238,3244,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5819 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5819 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5819 4 (fun x => (if x<3164 then (if x<1764 then (if x<1714 then 0 else (if x<1720 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3252 then (if x<3238 then 2 else (if x<3244 then 0 else 1)) else (if x<3304 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5820 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,3072,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5820 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5820 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5820 1594 4
  · have he : independentCachedBranchMembers5820.erase 1594=independentCachedBranchMembers5818 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5818
  · have he : independentCachedBranchMembers5820.filter (independentCachedEdge 1594)=independentCachedBranchMembers5819 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5819
def independentCachedBranchMembers5821 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1720,1752,3132,3164,3178,3186,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5821 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5821 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5821 4 (fun x => (if x<3132 then (if x<1678 then (if x<1644 then (if x<1626 then 0 else 1) else (if x<1652 then 0 else 1)) else (if x<1720 then (if x<1686 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3238 then (if x<3178 then (if x<3164 then 2 else 3) else (if x<3186 then 2 else 3)) else (if x<3304 then (if x<3270 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5822 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,3072,3126,3132,3150,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5822 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5822 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5822 3298 4
  · have he : independentCachedBranchMembers5822.erase 3298=independentCachedBranchMembers5820 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5820
  · have he : independentCachedBranchMembers5822.filter (independentCachedEdge 3298)=independentCachedBranchMembers5821 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5821
def independentCachedBranchMembers5823 : Finset ℕ := ([1594,1644,1678,1692,1714,1738,1752,1764,3126,3150,3164,3186,3244,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5823 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5823 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5823 4 (fun x => (if x<3126 then (if x<1714 then (if x<1678 then (if x<1644 then 0 else 0) else (if x<1692 then 0 else 1)) else (if x<1752 then (if x<1738 then 1 else 1) else (if x<1764 then 0 else 1))) else (if x<3244 then (if x<3164 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3284 then (if x<3270 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
