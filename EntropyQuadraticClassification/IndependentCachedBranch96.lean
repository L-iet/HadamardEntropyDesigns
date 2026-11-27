/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch95
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5856 : Finset ℕ := ([1596,1626,1644,1650,1686,1708,1714,1734,1738,1748,1752,1776,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5856 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5856 3102 4
  · have he : independentCachedBranchMembers5856.erase 3102=independentCachedBranchMembers5854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5854
  · have he : independentCachedBranchMembers5856.filter (independentCachedEdge 3102)=independentCachedBranchMembers5855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5855
def independentCachedBranchMembers5857 : Finset ℕ := ([1650,1714,1734,1738,1776,3072,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5857 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5857 4 (fun x => (if x<3130 then (if x<1738 then (if x<1714 then 0 else (if x<1734 then 1 else 0)) else (if x<3072 then (if x<1776 then 1 else 2) else (if x<3126 then 3 else 1))) else (if x<3214 then (if x<3188 then (if x<3150 then 0 else 1) else (if x<3192 then 2 else 3)) else (if x<3256 then (if x<3252 then 0 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5858 : Finset ℕ := ([1734,1738,3072,3150,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5858 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5858 3 (fun x => (if x<3150 then (if x<1738 then 0 else (if x<3072 then 1 else 2)) else (if x<3214 then 0 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5859 : Finset ℕ := ([1596,1650,1714,1734,1738,1776,3072,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5859 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5859 1596 3
  · have he : independentCachedBranchMembers5859.erase 1596=independentCachedBranchMembers5857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5857
  · have he : independentCachedBranchMembers5859.filter (independentCachedEdge 1596)=independentCachedBranchMembers5858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5858
def independentCachedBranchMembers5860 : Finset ℕ := ([1596,1626,1644,1650,1686,1708,1714,1734,1738,1748,1752,1762,1776,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5860 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5860 1762 4
  · have he : independentCachedBranchMembers5860.erase 1762=independentCachedBranchMembers5856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5856
  · have he : independentCachedBranchMembers5860.filter (independentCachedEdge 1762)=independentCachedBranchMembers5859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5859
def independentCachedBranchMembers5861 : Finset ℕ := ([1644,1686,1714,1738,1752,3072,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5861 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5861 4 (fun x => (if x<3150 then (if x<1738 then (if x<1686 then 0 else (if x<1714 then 1 else 2)) else (if x<3072 then (if x<1752 then 0 else 1) else (if x<3126 then 3 else 1))) else (if x<3238 then (if x<3178 then (if x<3164 then 0 else 2) else (if x<3192 then 3 else 1)) else (if x<3276 then (if x<3252 then 3 else 2) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5862 : Finset ℕ := ([1738,1752,3072,3126,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5862 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5862 3 (fun x => (if x<3126 then (if x<1752 then 0 else (if x<3072 then 1 else 2)) else (if x<3276 then 0 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5863 : Finset ℕ := ([1626,1644,1686,1714,1738,1752,3072,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5863 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5863 1626 3
  · have he : independentCachedBranchMembers5863.erase 1626=independentCachedBranchMembers5861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5861
  · have he : independentCachedBranchMembers5863.filter (independentCachedEdge 1626)=independentCachedBranchMembers5862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5862
def independentCachedBranchMembers5864 : Finset ℕ := ([1596,1626,1644,1650,1686,1690,1708,1714,1734,1738,1748,1752,1762,1776,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5864 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5864 1690 4
  · have he : independentCachedBranchMembers5864.erase 1690=independentCachedBranchMembers5860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5860
  · have he : independentCachedBranchMembers5864.filter (independentCachedEdge 1690)=independentCachedBranchMembers5863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5863
def independentCachedBranchMembers5865 : Finset ℕ := ([1626,1650,1686,1708,1734,1748,3072,3130,3178,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5865 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5865 4 (fun x => (if x<3178 then (if x<1734 then (if x<1686 then (if x<1650 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<3072 then (if x<1748 then 1 else 2) else (if x<3130 then 3 else 1))) else (if x<3238 then (if x<3214 then (if x<3192 then 0 else 3) else (if x<3228 then 1 else 2)) else (if x<3276 then (if x<3252 then 0 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5866 : Finset ℕ := ([1596,1622,1626,1644,1650,1686,1690,1708,1714,1734,1738,1748,1752,1762,1776,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5866 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5866 1622 4
  · have he : independentCachedBranchMembers5866.erase 1622=independentCachedBranchMembers5864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5864
  · have he : independentCachedBranchMembers5866.filter (independentCachedEdge 1622)=independentCachedBranchMembers5865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5865
def independentCachedBranchMembers5867 : Finset ℕ := ([1596,1644,1708,1748,1752,1776,3072,3164,3188,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5867 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5867 4 (fun x => (if x<3188 then (if x<1752 then (if x<1708 then (if x<1644 then 0 else 1) else (if x<1748 then 2 else 0)) else (if x<3072 then (if x<1776 then 1 else 2) else (if x<3164 then 3 else 0))) else (if x<3256 then (if x<3228 then (if x<3192 then 3 else 1) else (if x<3252 then 3 else 0)) else (if x<3300 then (if x<3276 then 2 else 1) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5868 : Finset ℕ := ([1582,1596,1622,1626,1644,1650,1686,1690,1708,1714,1734,1738,1748,1752,1762,1776,3072,3102,3126,3130,3150,3164,3174,3178,3188,3192,3214,3228,3238,3242,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5868 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5868 1582 4
  · have he : independentCachedBranchMembers5868.erase 1582=independentCachedBranchMembers5866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5866
  · have he : independentCachedBranchMembers5868.filter (independentCachedEdge 1582)=independentCachedBranchMembers5867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5867
def independentCachedBranchMembers5869 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1746,1748,1752,1762,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5869 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5869 1746 5
  · have he : independentCachedBranchMembers5869.erase 1746=independentCachedBranchMembers5847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5847
  · have he : independentCachedBranchMembers5869.filter (independentCachedEdge 1746)=independentCachedBranchMembers5868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5868
def independentCachedBranchMembers5870 : Finset ℕ := ([1628,1644,1650,1678,1708,1714,1734,1738,1748,1752,1768,3072,3118,3132,3158,3162,3178,3188,3192,3222,3226,3238,3242,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5870 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5870 5 (fun x => (if x<3158 then (if x<1738 then (if x<1678 then (if x<1644 then 0 else (if x<1650 then 1 else 0)) else (if x<1714 then (if x<1708 then 1 else 2) else (if x<1734 then 2 else 0))) else (if x<1768 then (if x<1748 then 2 else (if x<1752 then 1 else 3)) else (if x<3118 then (if x<3072 then 0 else 4) else (if x<3132 then 1 else 4)))) else (if x<3238 then (if x<3188 then (if x<3162 then 0 else (if x<3178 then 3 else 4)) else (if x<3222 then (if x<3192 then 1 else 0) else (if x<3226 then 1 else 4))) else (if x<3276 then (if x<3242 then 4 else (if x<3256 then 2 else 3)) else (if x<3298 then (if x<3282 then 0 else 2) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5871 : Finset ℕ := ([1650,1714,1734,1748,3072,3158,3188,3222,3238,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5871 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5871 4 (fun x => (if x<3188 then (if x<1748 then (if x<1714 then 0 else (if x<1734 then 1 else 0)) else (if x<3072 then 1 else (if x<3158 then 2 else 0))) else (if x<3282 then (if x<3222 then 2 else (if x<3238 then 1 else 2)) else (if x<3298 then 2 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5872 : Finset ℕ := ([1594,1628,1644,1650,1678,1708,1714,1734,1738,1748,1752,1768,3072,3118,3132,3158,3162,3178,3188,3192,3222,3226,3238,3242,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5872 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5872 1594 4
  · have he : independentCachedBranchMembers5872.erase 1594=independentCachedBranchMembers5870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5870
  · have he : independentCachedBranchMembers5872.filter (independentCachedEdge 1594)=independentCachedBranchMembers5871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5871
def independentCachedBranchMembers5873 : Finset ℕ := ([1594,1628,1644,1650,1678,1734,1752,1768,3132,3162,3178,3188,3222,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5873 4 (fun x => (if x<3132 then (if x<1678 then (if x<1644 then (if x<1628 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<1768 then 1 else 0))) else (if x<3222 then (if x<3178 then (if x<3162 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5874 : Finset ℕ := ([1594,1628,1644,1650,1678,1708,1714,1734,1738,1748,1752,1768,3072,3118,3132,3158,3162,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5874 3252 4
  · have he : independentCachedBranchMembers5874.erase 3252=independentCachedBranchMembers5872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5872
  · have he : independentCachedBranchMembers5874.filter (independentCachedEdge 3252)=independentCachedBranchMembers5873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5873
def independentCachedBranchMembers5875 : Finset ℕ := ([1594,1628,1678,1708,1714,1738,1748,1768,3118,3158,3178,3188,3226,3238,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5875 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5875 4 (fun x => (if x<3118 then (if x<1714 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3226 then (if x<3178 then (if x<3158 then 2 else 2) else (if x<3188 then 3 else 3)) else (if x<3256 then (if x<3238 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5876 : Finset ℕ := ([1594,1628,1644,1650,1678,1708,1714,1734,1738,1748,1752,1768,3072,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5876 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5876 3174 4
  · have he : independentCachedBranchMembers5876.erase 3174=independentCachedBranchMembers5874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5874
  · have he : independentCachedBranchMembers5876.filter (independentCachedEdge 3174)=independentCachedBranchMembers5875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5875
def independentCachedBranchMembers5877 : Finset ℕ := ([1644,1650,1708,1714,1734,1738,1748,1752,3118,3132,3158,3162,3222,3226,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5877 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5877 4 (fun x => (if x<3118 then (if x<1734 then (if x<1708 then (if x<1650 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3222 then (if x<3158 then (if x<3132 then 2 else 3) else (if x<3162 then 2 else 3)) else (if x<3298 then (if x<3226 then 3 else 2) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5878 : Finset ℕ := ([1594,1628,1644,1650,1678,1708,1714,1734,1738,1748,1752,1768,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5878 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5878 3102 4
  · have he : independentCachedBranchMembers5878.erase 3102=independentCachedBranchMembers5876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5876
  · have he : independentCachedBranchMembers5878.filter (independentCachedEdge 3102)=independentCachedBranchMembers5877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5877
def independentCachedBranchMembers5879 : Finset ℕ := ([1644,1708,1734,1748,1768,3072,3118,3132,3158,3178,3192,3222,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5879 4 (fun x => (if x<3132 then (if x<1748 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<3072 then (if x<1768 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3222 then (if x<3178 then (if x<3158 then 0 else 1) else (if x<3192 then 2 else 3)) else (if x<3256 then (if x<3242 then 0 else 3) else (if x<3282 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5880 : Finset ℕ := ([1734,1748,3072,3158,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5880 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5880 3 (fun x => (if x<3158 then (if x<1748 then 0 else (if x<3072 then 1 else 2)) else (if x<3222 then 0 else (if x<3282 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5881 : Finset ℕ := ([1594,1644,1708,1734,1748,1768,3072,3118,3132,3158,3178,3192,3222,3242,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5881 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5881 1594 3
  · have he : independentCachedBranchMembers5881.erase 1594=independentCachedBranchMembers5879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5879
  · have he : independentCachedBranchMembers5881.filter (independentCachedEdge 1594)=independentCachedBranchMembers5880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5880
def independentCachedBranchMembers5882 : Finset ℕ := ([1594,1628,1644,1650,1678,1708,1714,1734,1738,1748,1752,1764,1768,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5882 1764 4
  · have he : independentCachedBranchMembers5882.erase 1764=independentCachedBranchMembers5878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5878
  · have he : independentCachedBranchMembers5882.filter (independentCachedEdge 1764)=independentCachedBranchMembers5881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5881
def independentCachedBranchMembers5883 : Finset ℕ := ([1650,1678,1708,1748,1752,3072,3118,3158,3162,3188,3192,3238,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5883 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5883 4 (fun x => (if x<3158 then (if x<1748 then (if x<1678 then 0 else (if x<1708 then 1 else 2)) else (if x<3072 then (if x<1752 then 0 else 1) else (if x<3118 then 3 else 1))) else (if x<3238 then (if x<3188 then (if x<3162 then 0 else 2) else (if x<3192 then 3 else 1)) else (if x<3282 then (if x<3242 then 3 else 2) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5884 : Finset ℕ := ([1748,1752,3072,3118,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5884 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5884 3 (fun x => (if x<3118 then (if x<1752 then 0 else (if x<3072 then 1 else 2)) else (if x<3282 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5885 : Finset ℕ := ([1628,1650,1678,1708,1748,1752,3072,3118,3158,3162,3188,3192,3238,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5885 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5885 1628 3
  · have he : independentCachedBranchMembers5885.erase 1628=independentCachedBranchMembers5883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5883
  · have he : independentCachedBranchMembers5885.filter (independentCachedEdge 1628)=independentCachedBranchMembers5884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5884
def independentCachedBranchMembers5886 : Finset ℕ := ([1594,1628,1644,1650,1678,1692,1708,1714,1734,1738,1748,1752,1764,1768,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5886 1692 4
  · have he : independentCachedBranchMembers5886.erase 1692=independentCachedBranchMembers5882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5882
  · have he : independentCachedBranchMembers5886.filter (independentCachedEdge 1692)=independentCachedBranchMembers5885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5885
def independentCachedBranchMembers5887 : Finset ℕ := ([1628,1644,1678,1714,1734,1738,3072,3132,3188,3192,3222,3226,3238,3242,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5887 4 (fun x => (if x<3188 then (if x<1734 then (if x<1678 then (if x<1644 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<3072 then (if x<1738 then 1 else 2) else (if x<3132 then 3 else 1))) else (if x<3238 then (if x<3222 then (if x<3192 then 0 else 3) else (if x<3226 then 1 else 2)) else (if x<3282 then (if x<3242 then 0 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
