/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch94
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5824 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,3072,3126,3132,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5824 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5824 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5824 3158 4
  · have he : independentCachedBranchMembers5824.erase 3158=independentCachedBranchMembers5822 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5822
  · have he : independentCachedBranchMembers5824.filter (independentCachedEdge 3158)=independentCachedBranchMembers5823 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5823
def independentCachedBranchMembers5825 : Finset ℕ := ([1626,1652,1686,1692,1714,1720,1738,1764,3126,3132,3150,3178,3238,3244,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5825 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5825 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5825 4 (fun x => (if x<3126 then (if x<1714 then (if x<1686 then (if x<1652 then 0 else 0) else (if x<1692 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 0) else (if x<1764 then 1 else 1))) else (if x<3238 then (if x<3150 then (if x<3132 then 2 else 3) else (if x<3178 then 2 else 3)) else (if x<3284 then (if x<3244 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5826 : Finset ℕ := ([1594,1626,1644,1652,1678,1686,1692,1714,1720,1738,1752,1764,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5826 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5826 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5826 3118 4
  · have he : independentCachedBranchMembers5826.erase 3118=independentCachedBranchMembers5824 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5824
  · have he : independentCachedBranchMembers5826.filter (independentCachedEdge 3118)=independentCachedBranchMembers5825 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5825
def independentCachedBranchMembers5827 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1748,1752,1762,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5827 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5827 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5827 1690 5
  · have he : independentCachedBranchMembers5827.erase 1690=independentCachedBranchMembers5817 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5817
  · have he : independentCachedBranchMembers5827.filter (independentCachedEdge 1690)=independentCachedBranchMembers5826 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5826
def independentCachedBranchMembers5828 : Finset ℕ := ([1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,3072,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5828 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5828 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5828 5 (fun x => (if x<3158 then (if x<1720 then (if x<1650 then (if x<1626 then 0 else (if x<1628 then 1 else 2)) else (if x<1686 then (if x<1652 then 0 else 1) else (if x<1708 then 0 else 2))) else (if x<1768 then (if x<1734 then 1 else (if x<1748 then 2 else 3)) else (if x<3130 then (if x<3072 then 3 else 4) else (if x<3132 then 4 else 2)))) else (if x<3250 then (if x<3192 then (if x<3178 then 0 else (if x<3180 then 0 else 4)) else (if x<3228 then (if x<3214 then 1 else 0) else (if x<3238 then 4 else 2))) else (if x<3276 then (if x<3252 then 0 else (if x<3274 then 1 else 4)) else (if x<3300 then (if x<3288 then 2 else 3) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5829 : Finset ℕ := ([1650,1652,1686,1768,3072,3178,3180,3192,3214,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5829 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5829 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5829 4 (fun x => (if x<3180 then (if x<1768 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<3072 then 1 else (if x<3178 then 2 else 0))) else (if x<3228 then (if x<3192 then 1 else (if x<3214 then 2 else 0)) else (if x<3300 then 2 else (if x<3312 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5830 : Finset ℕ := ([1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,3072,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5830 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5830 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5830 1590 4
  · have he : independentCachedBranchMembers5830.erase 1590=independentCachedBranchMembers5828 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5828
  · have he : independentCachedBranchMembers5830.filter (independentCachedEdge 1590)=independentCachedBranchMembers5829 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5829
def independentCachedBranchMembers5831 : Finset ℕ := ([1590,1614,1626,1652,1686,1708,1720,1748,3132,3178,3228,3238,3250,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5831 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5831 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5831 4 (fun x => (if x<3132 then (if x<1686 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1708 then 1 else 0) else (if x<1748 then 1 else 0))) else (if x<3250 then (if x<3228 then (if x<3178 then 2 else 2) else (if x<3238 then 3 else 2)) else (if x<3300 then (if x<3274 then 3 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5832 : Finset ℕ := ([1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,3072,3130,3132,3158,3178,3180,3192,3214,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5832 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5832 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5832 3298 4
  · have he : independentCachedBranchMembers5832.erase 3298=independentCachedBranchMembers5830 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5830
  · have he : independentCachedBranchMembers5832.filter (independentCachedEdge 3298)=independentCachedBranchMembers5831 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5831
def independentCachedBranchMembers5833 : Finset ℕ := ([1590,1614,1628,1650,1708,1734,1748,1768,3130,3180,3214,3228,3250,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5833 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5833 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5833 4 (fun x => (if x<3130 then (if x<1708 then (if x<1628 then (if x<1614 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1748 then (if x<1734 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<3250 then (if x<3214 then (if x<3180 then 2 else 2) else (if x<3228 then 2 else 3)) else (if x<3288 then (if x<3274 then 3 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5834 : Finset ℕ := ([1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,3072,3130,3132,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5834 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5834 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5834 3226 4
  · have he : independentCachedBranchMembers5834.erase 3226=independentCachedBranchMembers5832 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5832
  · have he : independentCachedBranchMembers5834.filter (independentCachedEdge 3226)=independentCachedBranchMembers5833 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5833
def independentCachedBranchMembers5835 : Finset ℕ := ([1626,1628,1650,1652,1686,1720,1734,1768,3130,3132,3178,3180,3214,3238,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5835 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5835 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5835 4 (fun x => (if x<3130 then (if x<1686 then (if x<1650 then (if x<1628 then 0 else 1) else (if x<1652 then 1 else 0)) else (if x<1734 then (if x<1720 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3214 then (if x<3178 then (if x<3132 then 2 else 3) else (if x<3180 then 3 else 2)) else (if x<3288 then (if x<3238 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5836 : Finset ℕ := ([1590,1614,1626,1628,1650,1652,1686,1708,1720,1734,1748,1768,3072,3118,3130,3132,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5836 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5836 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5836 3118 4
  · have he : independentCachedBranchMembers5836.erase 3118=independentCachedBranchMembers5834 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5834
  · have he : independentCachedBranchMembers5836.filter (independentCachedEdge 3118)=independentCachedBranchMembers5835 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5835
def independentCachedBranchMembers5837 : Finset ℕ := ([1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1748,1752,1762,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5837 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5837 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5837 1622 5
  · have he : independentCachedBranchMembers5837.erase 1622=independentCachedBranchMembers5827 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5827
  · have he : independentCachedBranchMembers5837.filter (independentCachedEdge 1622)=independentCachedBranchMembers5836 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5836
def independentCachedBranchMembers5838 : Finset ℕ := ([1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,3072,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5838 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5838 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5838 5 (fun x => (if x<3164 then (if x<1708 then (if x<1642 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1678 then (if x<1644 then 1 else 2) else (if x<1702 then 1 else 0))) else (if x<1776 then (if x<1748 then 3 else (if x<1752 then 2 else 1)) else (if x<3118 then (if x<3072 then 3 else 4) else (if x<3162 then 0 else 0)))) else (if x<3252 then (if x<3192 then (if x<3186 then 2 else (if x<3188 then 3 else 4)) else (if x<3228 then (if x<3222 then 1 else 2) else (if x<3250 then 1 else 0))) else (if x<3274 then (if x<3256 then 3 else (if x<3270 then 4 else 0)) else (if x<3300 then (if x<3276 then 1 else 4) else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5839 : Finset ℕ := ([1594,1596,1702,1752,3072,3162,3164,3192,3228,3256,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5839 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5839 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5839 4 (fun x => (if x<3164 then (if x<1752 then (if x<1596 then 0 else (if x<1702 then 1 else 0)) else (if x<3072 then 1 else (if x<3162 then 2 else 0))) else (if x<3256 then (if x<3192 then 1 else (if x<3228 then 2 else 2)) else (if x<3270 then 1 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5840 : Finset ℕ := ([1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,3072,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5840 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5840 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5840 1590 4
  · have he : independentCachedBranchMembers5840.erase 1590=independentCachedBranchMembers5838 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5838
  · have he : independentCachedBranchMembers5840.filter (independentCachedEdge 1590)=independentCachedBranchMembers5839 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5839
def independentCachedBranchMembers5841 : Finset ℕ := ([1590,1594,1614,1644,1678,1708,1748,1752,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5841 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5841 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5841 4 (fun x => (if x<3164 then (if x<1678 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1644 then 0 else 1)) else (if x<1748 then (if x<1708 then 1 else 0) else (if x<1752 then 0 else 1))) else (if x<3270 then (if x<3228 then (if x<3186 then 2 else 2) else (if x<3250 then 3 else 3)) else (if x<3300 then (if x<3274 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5842 : Finset ℕ := ([1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,3072,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5842 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5842 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5842 3298 4
  · have he : independentCachedBranchMembers5842.erase 3298=independentCachedBranchMembers5840 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5840
  · have he : independentCachedBranchMembers5842.filter (independentCachedEdge 3298)=independentCachedBranchMembers5841 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5841
def independentCachedBranchMembers5843 : Finset ℕ := ([1590,1596,1614,1642,1702,1708,1748,1776,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5843 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5843 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5843 4 (fun x => (if x<3162 then (if x<1702 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1642 then 0 else 1)) else (if x<1748 then (if x<1708 then 1 else 0) else (if x<1776 then 0 else 1))) else (if x<3250 then (if x<3222 then (if x<3188 then 2 else 2) else (if x<3228 then 2 else 3)) else (if x<3274 then (if x<3256 then 3 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5844 : Finset ℕ := ([1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,3072,3118,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5844 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5844 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5844 3226 4
  · have he : independentCachedBranchMembers5844.erase 3226=independentCachedBranchMembers5842 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5842
  · have he : independentCachedBranchMembers5844.filter (independentCachedEdge 3226)=independentCachedBranchMembers5843 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5843
def independentCachedBranchMembers5845 : Finset ℕ := ([1594,1596,1642,1644,1678,1702,1752,1776,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5845 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5845 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5845 4 (fun x => (if x<3162 then (if x<1678 then (if x<1642 then (if x<1596 then 0 else 1) else (if x<1644 then 1 else 0)) else (if x<1752 then (if x<1702 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3222 then (if x<3186 then (if x<3164 then 2 else 3) else (if x<3188 then 3 else 2)) else (if x<3270 then (if x<3256 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5846 : Finset ℕ := ([1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,3072,3118,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5846 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5846 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5846 3158 4
  · have he : independentCachedBranchMembers5846.erase 3158=independentCachedBranchMembers5844 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5844
  · have he : independentCachedBranchMembers5846.filter (independentCachedEdge 3158)=independentCachedBranchMembers5845 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5845
def independentCachedBranchMembers5847 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1748,1752,1762,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5847 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5847 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5847 1582 5
  · have he : independentCachedBranchMembers5847.erase 1582=independentCachedBranchMembers5837 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5837
  · have he : independentCachedBranchMembers5847.filter (independentCachedEdge 1582)=independentCachedBranchMembers5846 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5846
def independentCachedBranchMembers5848 : Finset ℕ := ([1626,1644,1650,1686,1708,1714,1734,1738,1748,1752,1776,3072,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5848 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5848 5 (fun x => (if x<3150 then (if x<1738 then (if x<1686 then (if x<1644 then 0 else (if x<1650 then 0 else 1)) else (if x<1714 then (if x<1708 then 1 else 2) else (if x<1734 then 2 else 0))) else (if x<1776 then (if x<1748 then 1 else (if x<1752 then 2 else 3)) else (if x<3126 then (if x<3072 then 0 else 4) else (if x<3130 then 1 else 4)))) else (if x<3238 then (if x<3188 then (if x<3164 then 0 else (if x<3178 then 3 else 1)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3228 then 1 else 4))) else (if x<3276 then (if x<3252 then 4 else (if x<3256 then 2 else 3)) else (if x<3300 then (if x<3282 then 2 else 0) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5849 : Finset ℕ := ([1644,1708,1734,1738,3072,3150,3178,3214,3238,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5849 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5849 4 (fun x => (if x<3178 then (if x<1738 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3276 then (if x<3214 then 2 else (if x<3238 then 1 else 2)) else (if x<3300 then 2 else (if x<3304 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5850 : Finset ℕ := ([1596,1626,1644,1650,1686,1708,1714,1734,1738,1748,1752,1776,3072,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5850 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5850 1596 4
  · have he : independentCachedBranchMembers5850.erase 1596=independentCachedBranchMembers5848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5848
  · have he : independentCachedBranchMembers5850.filter (independentCachedEdge 1596)=independentCachedBranchMembers5849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5849
def independentCachedBranchMembers5851 : Finset ℕ := ([1596,1626,1644,1650,1686,1734,1752,1776,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5851 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5851 4 (fun x => (if x<3130 then (if x<1686 then (if x<1644 then (if x<1626 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3214 then (if x<3178 then (if x<3164 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5852 : Finset ℕ := ([1596,1626,1644,1650,1686,1708,1714,1734,1738,1748,1752,1776,3072,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5852 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5852 3242 4
  · have he : independentCachedBranchMembers5852.erase 3242=independentCachedBranchMembers5850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5850
  · have he : independentCachedBranchMembers5852.filter (independentCachedEdge 3242)=independentCachedBranchMembers5851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5851
def independentCachedBranchMembers5853 : Finset ℕ := ([1596,1626,1686,1708,1714,1738,1748,1776,3126,3150,3178,3188,3228,3238,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5853 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5853 4 (fun x => (if x<3126 then (if x<1714 then (if x<1686 then (if x<1626 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3228 then (if x<3178 then (if x<3150 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5854 : Finset ℕ := ([1596,1626,1644,1650,1686,1708,1714,1734,1738,1748,1752,1776,3072,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5854 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5854 3174 4
  · have he : independentCachedBranchMembers5854.erase 3174=independentCachedBranchMembers5852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5852
  · have he : independentCachedBranchMembers5854.filter (independentCachedEdge 3174)=independentCachedBranchMembers5853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5853
def independentCachedBranchMembers5855 : Finset ℕ := ([1644,1650,1708,1714,1734,1738,1748,1752,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5855 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5855 4 (fun x => (if x<3126 then (if x<1734 then (if x<1708 then (if x<1650 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3214 then (if x<3150 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)) else (if x<3300 then (if x<3228 then 3 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
