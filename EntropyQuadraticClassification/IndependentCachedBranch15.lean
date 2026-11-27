/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch14
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1920 : Finset ℕ := ([48,72,1590,1594,1614,1644,1702,1776,2740,2764,3118,3162,3188,3192,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1920 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1920 5 (fun x => (if x<3118 then (if x<1644 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1594 then 0 else (if x<1614 then 1 else 0))) else (if x<1776 then (if x<1702 then 1 else 1) else (if x<2740 then 1 else (if x<2764 then 0 else 0)))) else (if x<3250 then (if x<3188 then (if x<3162 then 1 else 2) else (if x<3192 then 2 else (if x<3228 then 1 else 2))) else (if x<3274 then (if x<3270 then 0 else 2) else (if x<3300 then 0 else (if x<3304 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1921 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2680,2716,2738,2740,2762,2764,2788,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1921 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1921 2716 5
  · have he : independentCachedBranchMembers1921.erase 2716=independentCachedBranchMembers1919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1919
  · have he : independentCachedBranchMembers1921.filter (independentCachedEdge 2716)=independentCachedBranchMembers1920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1920
def independentCachedBranchMembers1922 : Finset ℕ := ([48,72,132,252,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1922 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1922 5 (fun x => (if x<3222 then (if x<3162 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else (if x<3118 then 0 else 1))) else (if x<3186 then (if x<3164 then 1 else 2) else (if x<3188 then 2 else (if x<3192 then 1 else 0)))) else (if x<3270 then (if x<3250 then (if x<3228 then 1 else 3) else (if x<3252 then 3 else (if x<3256 then 0 else 1))) else (if x<3276 then (if x<3274 then 2 else 3) else (if x<3300 then 0 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1923 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2680,2716,2738,2740,2762,2764,2788,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1923 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1923 2606 5
  · have he : independentCachedBranchMembers1923.erase 2606=independentCachedBranchMembers1921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1921
  · have he : independentCachedBranchMembers1923.filter (independentCachedEdge 2606)=independentCachedBranchMembers1922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1922
def independentCachedBranchMembers1924 : Finset ℕ := ([48,132,1594,1596,1614,1678,1702,1748,2680,2762,2764,2788,3118,3162,3164,3186,3188,3228,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1924 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1924 5 (fun x => (if x<2788 then (if x<1678 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1596 then 0 else (if x<1614 then 1 else 1))) else (if x<2680 then (if x<1702 then 0 else (if x<1748 then 1 else 1)) else (if x<2762 then 0 else (if x<2764 then 2 else 0)))) else (if x<3188 then (if x<3162 then (if x<3118 then 2 else 1) else (if x<3164 then 2 else (if x<3186 then 1 else 0))) else (if x<3252 then (if x<3228 then 2 else (if x<3250 then 3 else 3)) else (if x<3270 then 1 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1925 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2680,2716,2738,2740,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1925 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1925 2792 5
  · have he : independentCachedBranchMembers1925.erase 2792=independentCachedBranchMembers1923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1923
  · have he : independentCachedBranchMembers1925.filter (independentCachedEdge 2792)=independentCachedBranchMembers1924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1924
def independentCachedBranchMembers1926 : Finset ℕ := ([72,252,1590,1642,1644,1708,1752,1776,2680,2762,2764,2788,3118,3162,3164,3186,3188,3228,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1926 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1926 5 (fun x => (if x<2788 then (if x<1708 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1644 then 1 else 0))) else (if x<2680 then (if x<1752 then 1 else (if x<1776 then 0 else 1)) else (if x<2762 then 0 else (if x<2764 then 2 else 0)))) else (if x<3188 then (if x<3162 then (if x<3118 then 2 else 1) else (if x<3164 then 2 else (if x<3186 then 0 else 1))) else (if x<3252 then (if x<3228 then 2 else (if x<3250 then 3 else 3)) else (if x<3270 then 1 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1927 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2680,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1927 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1927 2758 5
  · have he : independentCachedBranchMembers1927.erase 2758=independentCachedBranchMembers1925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1925
  · have he : independentCachedBranchMembers1927.filter (independentCachedEdge 2758)=independentCachedBranchMembers1926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1926
def independentCachedBranchMembers1928 : Finset ℕ := ([72,252,1596,1614,1644,1702,1748,1752,2680,2716,2738,2764,3118,3164,3186,3222,3252,3256,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1928 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1928 5 (fun x => (if x<2764 then (if x<1702 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1614 then 1 else (if x<1644 then 1 else 0))) else (if x<2680 then (if x<1748 then 1 else (if x<1752 then 1 else 0)) else (if x<2716 then 0 else (if x<2738 then 2 else 2)))) else (if x<3252 then (if x<3164 then (if x<3118 then 0 else 1) else (if x<3186 then 0 else (if x<3222 then 2 else 2))) else (if x<3274 then (if x<3256 then 1 else (if x<3270 then 2 else 1)) else (if x<3300 then 3 else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1929 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2674,2680,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1929 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1929 2674 5
  · have he : independentCachedBranchMembers1929.erase 2674=independentCachedBranchMembers1927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1927
  · have he : independentCachedBranchMembers1929.filter (independentCachedEdge 2674)=independentCachedBranchMembers1928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1928
def independentCachedBranchMembers1930 : Finset ℕ := ([48,132,1590,1594,1642,1678,1708,1776,2680,2716,2738,2764,3118,3164,3186,3222,3252,3256,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1930 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1930 5 (fun x => (if x<2764 then (if x<1678 then (if x<1590 then (if x<132 then 0 else 0) else (if x<1594 then 1 else (if x<1642 then 0 else 1))) else (if x<2680 then (if x<1708 then 0 else (if x<1776 then 1 else 1)) else (if x<2716 then 0 else (if x<2738 then 2 else 2)))) else (if x<3252 then (if x<3164 then (if x<3118 then 0 else 1) else (if x<3186 then 2 else (if x<3222 then 0 else 2))) else (if x<3274 then (if x<3256 then 1 else (if x<3270 then 2 else 0)) else (if x<3300 then 3 else (if x<3304 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1931 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2652,2674,2680,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1931 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1931 2652 5
  · have he : independentCachedBranchMembers1931.erase 2652=independentCachedBranchMembers1929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1929
  · have he : independentCachedBranchMembers1931.filter (independentCachedEdge 2652)=independentCachedBranchMembers1930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1930
def independentCachedBranchMembers1932 : Finset ℕ := ([48,252,1594,1596,1614,1708,1752,1776,2680,2716,2738,2740,2758,2792,3118,3162,3164,3186,3188,3222,3256,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1932 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1932 5 (fun x => (if x<2758 then (if x<1752 then (if x<1596 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1614 then 0 else (if x<1708 then 1 else 1))) else (if x<2716 then (if x<1776 then 1 else (if x<2680 then 0 else 0)) else (if x<2738 then 2 else (if x<2740 then 2 else 0)))) else (if x<3188 then (if x<3162 then (if x<2792 then 2 else (if x<3118 then 2 else 1)) else (if x<3164 then 1 else (if x<3186 then 3 else 3))) else (if x<3274 then (if x<3222 then 0 else (if x<3256 then 2 else 0)) else (if x<3276 then 3 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1933 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2652,2674,2680,2710,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1933 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1933 2710 5
  · have he : independentCachedBranchMembers1933.erase 2710=independentCachedBranchMembers1931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1931
  · have he : independentCachedBranchMembers1933.filter (independentCachedEdge 2710)=independentCachedBranchMembers1932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1932
def independentCachedBranchMembers1934 : Finset ℕ := ([48,252,1590,1596,1644,1678,1748,1776,2652,2674,2680,2740,2762,2788,3118,3162,3188,3222,3228,3250,3256,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1934 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1934 5 (fun x => (if x<2762 then (if x<1748 then (if x<1596 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 0 else (if x<1678 then 1 else 1))) else (if x<2674 then (if x<1776 then 1 else (if x<2652 then 0 else 2)) else (if x<2680 then 2 else (if x<2740 then 0 else 0)))) else (if x<3228 then (if x<3162 then (if x<2788 then 2 else (if x<3118 then 2 else 1)) else (if x<3188 then 2 else (if x<3222 then 0 else 1))) else (if x<3270 then (if x<3250 then 3 else (if x<3256 then 3 else 0)) else (if x<3276 then 3 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1935 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2650,2652,2674,2680,2710,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1935 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1935 2650 5
  · have he : independentCachedBranchMembers1935.erase 2650=independentCachedBranchMembers1933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1933
  · have he : independentCachedBranchMembers1935.filter (independentCachedEdge 2650)=independentCachedBranchMembers1934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1934
def independentCachedBranchMembers1936 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1642,1702,1708,1748,1776,2710,2716,2738,2762,2788,3118,3164,3186,3192,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1936 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1936 5 (fun x => (if x<2710 then (if x<1614 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1590 then 0 else (if x<1596 then 1 else 2))) else (if x<1708 then (if x<1642 then 1 else (if x<1702 then 2 else 2)) else (if x<1748 then 1 else (if x<1776 then 1 else 2)))) else (if x<3164 then (if x<2762 then (if x<2716 then 3 else (if x<2738 then 4 else 4)) else (if x<2788 then 3 else (if x<3118 then 3 else 1))) else (if x<3252 then (if x<3186 then 4 else (if x<3192 then 4 else 0)) else (if x<3276 then (if x<3270 then 0 else 3) else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1937 : Finset ℕ := ([48,252,1590,1596,1748,1776,2762,2788,3118,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1937 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1937 4 (fun x => (if x<2762 then (if x<1596 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1748 then 0 else (if x<1776 then 1 else 0))) else (if x<3270 then (if x<2788 then 2 else (if x<3118 then 2 else 1)) else (if x<3276 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1938 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1642,1702,1708,1748,1776,2650,2710,2716,2738,2762,2788,3118,3164,3186,3192,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1938 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1938 2650 4
  · have he : independentCachedBranchMembers1938.erase 2650=independentCachedBranchMembers1936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1936
  · have he : independentCachedBranchMembers1938.filter (independentCachedEdge 2650)=independentCachedBranchMembers1937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1937
def independentCachedBranchMembers1939 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1939 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1939 2714 5
  · have he : independentCachedBranchMembers1939.erase 2714=independentCachedBranchMembers1935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1935
  · have he : independentCachedBranchMembers1939.filter (independentCachedEdge 2714)=independentCachedBranchMembers1938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1938
def independentCachedBranchMembers1940 : Finset ℕ := ([48,72,132,252,1594,1596,1642,1644,1678,1702,1752,1776,2652,2674,2710,2758,2792,3118,3192,3228,3250,3252,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1940 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1940 5 (fun x => (if x<2652 then (if x<1642 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1594 then 0 else (if x<1596 then 1 else 2))) else (if x<1702 then (if x<1644 then 2 else (if x<1678 then 1 else 1)) else (if x<1752 then 2 else (if x<1776 then 1 else 2)))) else (if x<3192 then (if x<2758 then (if x<2674 then 3 else (if x<2710 then 3 else 3)) else (if x<2792 then 4 else (if x<3118 then 4 else 1))) else (if x<3252 then (if x<3228 then 0 else (if x<3250 then 3 else 3)) else (if x<3276 then (if x<3274 then 0 else 4) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1941 : Finset ℕ := ([48,252,1596,1644,1678,1776,2652,2674,3118,3228,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1941 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1941 4 (fun x => (if x<2652 then (if x<1644 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1678 then 1 else (if x<1776 then 1 else 0))) else (if x<3228 then (if x<2674 then 2 else (if x<3118 then 2 else 1)) else (if x<3250 then 2 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1942 : Finset ℕ := ([48,72,132,252,1594,1596,1642,1644,1678,1702,1752,1776,2650,2652,2674,2710,2758,2792,3118,3192,3228,3250,3252,3274,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1942 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1942 2650 4
  · have he : independentCachedBranchMembers1942.erase 2650=independentCachedBranchMembers1940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1940
  · have he : independentCachedBranchMembers1942.filter (independentCachedEdge 2650)=independentCachedBranchMembers1941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1941
def independentCachedBranchMembers1943 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1943 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1943 2646 5
  · have he : independentCachedBranchMembers1943.erase 2646=independentCachedBranchMembers1939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1939
  · have he : independentCachedBranchMembers1943.filter (independentCachedEdge 2646)=independentCachedBranchMembers1942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1942
def independentCachedBranchMembers1944 : Finset ℕ := ([72,132,252,1596,1644,1708,1748,1752,1776,2680,2716,2740,2764,2792,3164,3188,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1944 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1944 5 (fun x => (if x<2740 then (if x<1708 then (if x<252 then (if x<132 then 0 else 0) else (if x<1596 then 0 else (if x<1644 then 1 else 2))) else (if x<1776 then (if x<1748 then 3 else (if x<1752 then 1 else 2)) else (if x<2680 then 3 else (if x<2716 then 0 else 1)))) else (if x<3228 then (if x<3164 then (if x<2764 then 0 else (if x<2792 then 0 else 2)) else (if x<3188 then 1 else (if x<3192 then 4 else 2))) else (if x<3276 then (if x<3252 then 4 else (if x<3256 then 1 else 3)) else (if x<3300 then 2 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1945 : Finset ℕ := ([72,1596,1752,2740,2764,2792,3164,3192,3228,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1945 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1945 4 (fun x => (if x<2792 then (if x<1752 then (if x<1596 then 0 else 1) else (if x<2740 then 0 else (if x<2764 then 1 else 0))) else (if x<3228 then (if x<3164 then 2 else (if x<3192 then 0 else 2)) else (if x<3256 then 1 else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1946 : Finset ℕ := ([72,132,252,1596,1644,1708,1748,1752,1776,2680,2716,2740,2764,2788,2792,3164,3188,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1946 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1946 2788 4
  · have he : independentCachedBranchMembers1946.erase 2788=independentCachedBranchMembers1944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1944
  · have he : independentCachedBranchMembers1946.filter (independentCachedEdge 2788)=independentCachedBranchMembers1945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1945
def independentCachedBranchMembers1947 : Finset ℕ := ([132,1708,1776,2680,2716,2764,3164,3252,3256,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1947 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1947 4 (fun x => (if x<2764 then (if x<1776 then (if x<1708 then 0 else 0) else (if x<2680 then 1 else (if x<2716 then 1 else 0))) else (if x<3256 then (if x<3164 then 2 else (if x<3252 then 2 else 0)) else (if x<3300 then 1 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1948 : Finset ℕ := ([72,132,252,1596,1644,1708,1748,1752,1776,2652,2680,2716,2740,2764,2788,2792,3164,3188,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1948 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1948 2652 4
  · have he : independentCachedBranchMembers1948.erase 2652=independentCachedBranchMembers1946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1946
  · have he : independentCachedBranchMembers1948.filter (independentCachedEdge 2652)=independentCachedBranchMembers1947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1947
def independentCachedBranchMembers1949 : Finset ℕ := ([1644,1708,1748,1752,2652,2716,2788,2792,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1949 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1949 4 (fun x => (if x<2788 then (if x<1752 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then 1 else (if x<2716 then 0 else 1))) else (if x<3228 then (if x<2792 then 0 else (if x<3164 then 1 else 2)) else (if x<3300 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1950 : Finset ℕ := ([48,72,132,252,1596,1644,1708,1748,1752,1776,2652,2680,2716,2740,2764,2788,2792,3164,3188,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1950 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1950 48 4
  · have he : independentCachedBranchMembers1950.erase 48=independentCachedBranchMembers1948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1948
  · have he : independentCachedBranchMembers1950.filter (independentCachedEdge 48)=independentCachedBranchMembers1949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1949
def independentCachedBranchMembers1951 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1951 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1951 1746 5
  · have he : independentCachedBranchMembers1951.erase 1746=independentCachedBranchMembers1943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1943
  · have he : independentCachedBranchMembers1951.filter (independentCachedEdge 1746)=independentCachedBranchMembers1950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1950
def independentCachedBranchMembers1952 : Finset ℕ := ([48,252,1590,1594,1596,1642,1644,1702,1708,1776,2606,2674,2680,2738,2740,2788,2792,3118,3186,3188,3192,3250,3252,3256,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1952 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1952 5 (fun x => (if x<2738 then (if x<1644 then (if x<1594 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1596 then 2 else (if x<1642 then 0 else 1))) else (if x<1776 then (if x<1702 then 2 else (if x<1708 then 2 else 1)) else (if x<2674 then (if x<2606 then 0 else 1) else (if x<2680 then 1 else 0)))) else (if x<3188 then (if x<2792 then (if x<2740 then 2 else (if x<2788 then 0 else 2)) else (if x<3118 then 1 else (if x<3186 then 3 else 3))) else (if x<3252 then (if x<3192 then 0 else (if x<3250 then 4 else 4)) else (if x<3300 then (if x<3256 then 3 else 0) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1953 : Finset ℕ := ([48,72,132,222,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1953 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1953 222 5
  · have he : independentCachedBranchMembers1953.erase 222=independentCachedBranchMembers1951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1951
  · have he : independentCachedBranchMembers1953.filter (independentCachedEdge 222)=independentCachedBranchMembers1952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1952
def independentCachedBranchMembers1954 : Finset ℕ := ([48,252,1596,1614,1642,1678,1702,1748,1752,1776,2606,2652,2680,2716,2740,2758,2762,3118,3164,3188,3192,3228,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1954 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1954 5 (fun x => (if x<2716 then (if x<1702 then (if x<1614 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1642 then 1 else (if x<1678 then 2 else 2))) else (if x<1776 then (if x<1748 then 1 else (if x<1752 then 1 else 2)) else (if x<2652 then (if x<2606 then 0 else 1) else (if x<2680 then 1 else 0)))) else (if x<3188 then (if x<2762 then (if x<2740 then 2 else (if x<2758 then 0 else 1)) else (if x<3118 then 2 else (if x<3164 then 3 else 3))) else (if x<3252 then (if x<3192 then 0 else (if x<3228 then 4 else 4)) else (if x<3270 then (if x<3256 then 3 else 0) else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1955 : Finset ℕ := ([18,48,72,132,222,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1955 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1955 18 5
  · have he : independentCachedBranchMembers1955.erase 18=independentCachedBranchMembers1953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1953
  · have he : independentCachedBranchMembers1955.filter (independentCachedEdge 18)=independentCachedBranchMembers1954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1954
def independentCachedBranchMembers1956 : Finset ℕ := ([18,72,132,222,1590,1594,1614,1644,1678,1708,1748,1752,2606,2646,2650,2680,2710,2714,2740,2764,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1956 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1956 5 (fun x => (if x<2650 then (if x<1644 then (if x<222 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1594 then (if x<1590 then 0 else 1) else (if x<1614 then 2 else 1))) else (if x<1748 then (if x<1678 then 2 else (if x<1708 then 2 else 1)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2646 then 1 else 1)))) else (if x<3186 then (if x<2714 then (if x<2680 then 0 else (if x<2710 then 2 else 0)) else (if x<2764 then (if x<2740 then 2 else 1) else (if x<3164 then 0 else 3))) else (if x<3270 then (if x<3228 then 3 else (if x<3250 then 4 else 4)) else (if x<3300 then (if x<3274 then 3 else 4) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1957 : Finset ℕ := ([18,222,1590,1594,1614,1678,2646,2650,2710,2714,3186,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1957 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1957 4 (fun x => (if x<2650 then (if x<1594 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1678 then (if x<1614 then 2 else 1) else (if x<2646 then 2 else 0))) else (if x<3186 then (if x<2710 then 3 else (if x<2714 then 3 else 0)) else (if x<3270 then (if x<3250 then 2 else 1) else (if x<3274 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1958 : Finset ℕ := ([18,222,3186,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1958 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1958 3 (fun x => (if x<3250 then (if x<222 then 0 else (if x<3186 then 0 else 1)) else (if x<3270 then 2 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1959 : Finset ℕ := ([18,222,1590,1594,1614,1678,2606,2646,2650,2710,2714,3186,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1959 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1959 2606 3
  · have he : independentCachedBranchMembers1959.erase 2606=independentCachedBranchMembers1957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1957
  · have he : independentCachedBranchMembers1959.filter (independentCachedEdge 2606)=independentCachedBranchMembers1958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1958
def independentCachedBranchMembers1960 : Finset ℕ := ([18,72,132,222,252,1590,1594,1614,1644,1678,1708,1748,1752,2606,2646,2650,2680,2710,2714,2740,2764,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1960 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1960 252 4
  · have he : independentCachedBranchMembers1960.erase 252=independentCachedBranchMembers1956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1956
  · have he : independentCachedBranchMembers1960.filter (independentCachedEdge 252)=independentCachedBranchMembers1959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1959
def independentCachedBranchMembers1961 : Finset ℕ := ([18,222,1644,1708,1748,1752,2650,2710,2714,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1961 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1961 4 (fun x => (if x<2650 then (if x<1708 then (if x<222 then 0 else (if x<1644 then 0 else 1)) else (if x<1748 then 2 else (if x<1752 then 1 else 2))) else (if x<3164 then (if x<2710 then 0 else (if x<2714 then 0 else 3)) else (if x<3300 then (if x<3228 then 1 else 2) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1962 : Finset ℕ := ([1644,1752,2650,2710,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1962 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1962 3 (fun x => (if x<2710 then (if x<1752 then 0 else (if x<2650 then 0 else 1)) else (if x<3228 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1963 : Finset ℕ := ([18,222,1644,1708,1748,1752,2646,2650,2710,2714,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1963 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1963 2646 3
  · have he : independentCachedBranchMembers1963.erase 2646=independentCachedBranchMembers1961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1961
  · have he : independentCachedBranchMembers1963.filter (independentCachedEdge 2646)=independentCachedBranchMembers1962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1962
def independentCachedBranchMembers1964 : Finset ℕ := ([18,222,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1964 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1964 3 (fun x => (if x<3228 then (if x<222 then 0 else (if x<3164 then 0 else 1)) else (if x<3300 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1965 : Finset ℕ := ([18,222,1644,1708,1748,1752,2606,2646,2650,2710,2714,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1965 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1965 2606 3
  · have he : independentCachedBranchMembers1965.erase 2606=independentCachedBranchMembers1963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1963
  · have he : independentCachedBranchMembers1965.filter (independentCachedEdge 2606)=independentCachedBranchMembers1964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1964
def independentCachedBranchMembers1966 : Finset ℕ := ([18,48,72,132,222,252,1590,1594,1614,1644,1678,1708,1748,1752,2606,2646,2650,2680,2710,2714,2740,2764,3164,3186,3228,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1966 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1966 48 4
  · have he : independentCachedBranchMembers1966.erase 48=independentCachedBranchMembers1960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1960
  · have he : independentCachedBranchMembers1966.filter (independentCachedEdge 48)=independentCachedBranchMembers1965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1965
def independentCachedBranchMembers1967 : Finset ℕ := ([18,48,72,132,222,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1967 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1967 3298 5
  · have he : independentCachedBranchMembers1967.erase 3298=independentCachedBranchMembers1955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1955
  · have he : independentCachedBranchMembers1967.filter (independentCachedEdge 3298)=independentCachedBranchMembers1966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1966
def independentCachedBranchMembers1968 : Finset ℕ := ([1590,1596,1614,1642,1702,1708,1748,1776,2606,2652,2674,2680,2714,2740,2758,2764,2792,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1968 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1968 5 (fun x => (if x<2714 then (if x<1748 then (if x<1642 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1702 then 1 else (if x<1708 then 1 else 0))) else (if x<2652 then (if x<1776 then 0 else (if x<2606 then 1 else 0)) else (if x<2674 then 2 else (if x<2680 then 2 else 1)))) else (if x<3188 then (if x<2764 then (if x<2740 then 2 else (if x<2758 then 0 else 2)) else (if x<2792 then 0 else (if x<3162 then 2 else 3))) else (if x<3250 then (if x<3222 then 3 else (if x<3228 then 3 else 4)) else (if x<3274 then (if x<3256 then 4 else 3) else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1969 : Finset ℕ := ([1590,1614,1642,1702,2606,2674,2714,2758,3162,3222,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1969 4 (fun x => (if x<2714 then (if x<1702 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<2606 then 1 else (if x<2674 then 0 else 2))) else (if x<3222 then (if x<2758 then 2 else (if x<3162 then 2 else 1)) else (if x<3250 then 1 else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1970 : Finset ℕ := ([252,1590,1596,1614,1642,1702,1708,1748,1776,2606,2652,2674,2680,2714,2740,2758,2764,2792,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1970 252 4
  · have he : independentCachedBranchMembers1970.erase 252=independentCachedBranchMembers1968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1968
  · have he : independentCachedBranchMembers1970.filter (independentCachedEdge 252)=independentCachedBranchMembers1969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1969
def independentCachedBranchMembers1971 : Finset ℕ := ([1590,1596,1614,1776,2606,2652,2714,2792,3188,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1971 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1971 4 (fun x => (if x<2714 then (if x<1776 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<2606 then 1 else (if x<2652 then 0 else 2))) else (if x<3250 then (if x<2792 then 2 else (if x<3188 then 2 else 1)) else (if x<3256 then 3 else (if x<3274 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1972 : Finset ℕ := ([132,252,1590,1596,1614,1642,1702,1708,1748,1776,2606,2652,2674,2680,2714,2740,2758,2764,2792,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1972 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1972 132 4
  · have he : independentCachedBranchMembers1972.erase 132=independentCachedBranchMembers1970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1970
  · have he : independentCachedBranchMembers1972.filter (independentCachedEdge 132)=independentCachedBranchMembers1971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1971
def independentCachedBranchMembers1973 : Finset ℕ := ([1596,1708,1748,1776,2606,2674,2714,2758,3188,3228,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1973 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1973 4 (fun x => (if x<2714 then (if x<1776 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2606 then 1 else (if x<2674 then 0 else 1))) else (if x<3228 then (if x<2758 then 2 else (if x<3188 then 0 else 2)) else (if x<3256 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1974 : Finset ℕ := ([72,132,252,1590,1596,1614,1642,1702,1708,1748,1776,2606,2652,2674,2680,2714,2740,2758,2764,2792,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1974 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1974 72 4
  · have he : independentCachedBranchMembers1974.erase 72=independentCachedBranchMembers1972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1972
  · have he : independentCachedBranchMembers1974.filter (independentCachedEdge 72)=independentCachedBranchMembers1973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1973
def independentCachedBranchMembers1975 : Finset ℕ := ([1642,1702,1708,1748,2606,2652,2714,2792,3162,3222,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1975 4 (fun x => (if x<2714 then (if x<1748 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<2606 then 1 else (if x<2652 then 0 else 2))) else (if x<3222 then (if x<2792 then 2 else (if x<3162 then 2 else 3)) else (if x<3228 then 3 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1976 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1642,1702,1708,1748,1776,2606,2652,2674,2680,2714,2740,2758,2764,2792,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1976 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1976 48 4
  · have he : independentCachedBranchMembers1976.erase 48=independentCachedBranchMembers1974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1974
  · have he : independentCachedBranchMembers1976.filter (independentCachedEdge 48)=independentCachedBranchMembers1975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1975
def independentCachedBranchMembers1977 : Finset ℕ := ([48,72,132,252,1596,1642,1702,1776,2652,2674,2758,2792,3228,3250,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1977 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1977 4 (fun x => (if x<2652 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1642 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3228 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3274 then (if x<3250 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1978 : Finset ℕ := ([48,72,132,252,1590,1596,1614,1642,1702,1708,1748,1776,2606,2646,2652,2674,2680,2714,2740,2758,2764,2792,3162,3188,3222,3228,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1978 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1978 2646 4
  · have he : independentCachedBranchMembers1978.erase 2646=independentCachedBranchMembers1976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1976
  · have he : independentCachedBranchMembers1978.filter (independentCachedEdge 2646)=independentCachedBranchMembers1977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1977
def independentCachedBranchMembers1979 : Finset ℕ := ([18,48,72,132,222,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1979 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1979 3226 5
  · have he : independentCachedBranchMembers1979.erase 3226=independentCachedBranchMembers1967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1967
  · have he : independentCachedBranchMembers1979.filter (independentCachedEdge 3226)=independentCachedBranchMembers1978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1978
def independentCachedBranchMembers1980 : Finset ℕ := ([1594,1596,1642,1644,1678,1702,1752,1776,2606,2646,2680,2716,2738,2740,2762,2764,2788,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1980 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1980 5 (fun x => (if x<2738 then (if x<1752 then (if x<1644 then (if x<1596 then 0 else (if x<1642 then 1 else 1)) else (if x<1678 then 0 else (if x<1702 then 0 else 1))) else (if x<2646 then (if x<1776 then 0 else (if x<2606 then 1 else 0)) else (if x<2680 then 2 else (if x<2716 then 0 else 2)))) else (if x<3164 then (if x<2764 then (if x<2740 then 2 else (if x<2762 then 1 else 2)) else (if x<2788 then 0 else (if x<3162 then 2 else 3))) else (if x<3222 then (if x<3186 then 4 else (if x<3188 then 4 else 3)) else (if x<3270 then (if x<3256 then 3 else 3) else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1981 : Finset ℕ := ([1594,1642,1678,1702,2606,2646,2738,2762,3162,3186,3222,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1981 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1981 4 (fun x => (if x<2738 then (if x<1702 then (if x<1642 then 0 else (if x<1678 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 0 else 2))) else (if x<3186 then (if x<2762 then 2 else (if x<3162 then 2 else 1)) else (if x<3222 then 3 else (if x<3270 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1982 : Finset ℕ := ([252,1594,1596,1642,1644,1678,1702,1752,1776,2606,2646,2680,2716,2738,2740,2762,2764,2788,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1982 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1982 252 4
  · have he : independentCachedBranchMembers1982.erase 252=independentCachedBranchMembers1980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1980
  · have he : independentCachedBranchMembers1982.filter (independentCachedEdge 252)=independentCachedBranchMembers1981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1981
def independentCachedBranchMembers1983 : Finset ℕ := ([1596,1644,1752,1776,2606,2646,2738,2762,3164,3188,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1983 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1983 4 (fun x => (if x<2738 then (if x<1776 then (if x<1644 then 0 else (if x<1752 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 0 else 2))) else (if x<3188 then (if x<2762 then 1 else (if x<3164 then 0 else 2)) else (if x<3256 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1984 : Finset ℕ := ([132,252,1594,1596,1642,1644,1678,1702,1752,1776,2606,2646,2680,2716,2738,2740,2762,2764,2788,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1984 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1984 132 4
  · have he : independentCachedBranchMembers1984.erase 132=independentCachedBranchMembers1982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1982
  · have he : independentCachedBranchMembers1984.filter (independentCachedEdge 132)=independentCachedBranchMembers1983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1983
def independentCachedBranchMembers1985 : Finset ℕ := ([1594,1596,1678,1776,2606,2646,2716,2788,3186,3188,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1985 4 (fun x => (if x<2716 then (if x<1776 then (if x<1596 then 0 else (if x<1678 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 0 else 2))) else (if x<3188 then (if x<2788 then 2 else (if x<3186 then 2 else 3)) else (if x<3256 then 1 else (if x<3270 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1986 : Finset ℕ := ([72,132,252,1594,1596,1642,1644,1678,1702,1752,1776,2606,2646,2680,2716,2738,2740,2762,2764,2788,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1986 72 4
  · have he : independentCachedBranchMembers1986.erase 72=independentCachedBranchMembers1984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1984
  · have he : independentCachedBranchMembers1986.filter (independentCachedEdge 72)=independentCachedBranchMembers1985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1985
def independentCachedBranchMembers1987 : Finset ℕ := ([1642,1644,1702,1752,2606,2646,2716,2788,3162,3164,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1987 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1987 4 (fun x => (if x<2716 then (if x<1752 then (if x<1644 then 0 else (if x<1702 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 0 else 2))) else (if x<3164 then (if x<2788 then 2 else (if x<3162 then 2 else 3)) else (if x<3222 then 1 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1988 : Finset ℕ := ([48,72,132,252,1594,1596,1642,1644,1678,1702,1752,1776,2606,2646,2680,2716,2738,2740,2762,2764,2788,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1988 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1988 48 4
  · have he : independentCachedBranchMembers1988.erase 48=independentCachedBranchMembers1986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1986
  · have he : independentCachedBranchMembers1988.filter (independentCachedEdge 48)=independentCachedBranchMembers1987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1987
def independentCachedBranchMembers1989 : Finset ℕ := ([48,72,132,252,1596,1642,1702,1776,2716,2738,2762,2788,3164,3186,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1989 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1989 4 (fun x => (if x<2716 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1642 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3164 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1990 : Finset ℕ := ([48,72,132,252,1594,1596,1642,1644,1678,1702,1752,1776,2606,2646,2680,2714,2716,2738,2740,2762,2764,2788,3162,3164,3186,3188,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1990 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1990 2714 4
  · have he : independentCachedBranchMembers1990.erase 2714=independentCachedBranchMembers1988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1988
  · have he : independentCachedBranchMembers1990.filter (independentCachedEdge 2714)=independentCachedBranchMembers1989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1989
def independentCachedBranchMembers1991 : Finset ℕ := ([18,48,72,132,222,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2788,2792,3118,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1991 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1991 3158 5
  · have he : independentCachedBranchMembers1991.erase 3158=independentCachedBranchMembers1979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1979
  · have he : independentCachedBranchMembers1991.filter (independentCachedEdge 3158)=independentCachedBranchMembers1990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1990
def independentCachedBranchMembers1992 : Finset ℕ := ([132,252,1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792,3118,3162,3188,3192,3222,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1992 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1992 5 (fun x => (if x<2738 then (if x<1678 then (if x<1594 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1614 then 2 else (if x<1644 then 1 else 2))) else (if x<1752 then (if x<1708 then 2 else (if x<1748 then 0 else 0)) else (if x<2674 then (if x<2652 then 2 else 3) else (if x<2716 then 3 else 0)))) else (if x<3188 then (if x<2788 then (if x<2758 then 1 else (if x<2762 then 3 else 1)) else (if x<3118 then (if x<2792 then 0 else 3) else (if x<3162 then 2 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3222 then 2 else 4)) else (if x<3276 then (if x<3256 then 0 else 4) else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1993 : Finset ℕ := ([1594,1678,1708,1748,2674,2716,2758,2788,3118,3188,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1993 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1993 4 (fun x => (if x<2758 then (if x<1748 then (if x<1678 then 0 else (if x<1708 then 0 else 1)) else (if x<2674 then 1 else (if x<2716 then 0 else 1))) else (if x<3188 then (if x<2788 then 0 else (if x<3118 then 1 else 2)) else (if x<3256 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1994 : Finset ℕ := ([72,132,252,1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792,3118,3162,3188,3192,3222,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1994 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1994 72 4
  · have he : independentCachedBranchMembers1994.erase 72=independentCachedBranchMembers1992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1992
  · have he : independentCachedBranchMembers1994.filter (independentCachedEdge 72)=independentCachedBranchMembers1993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1993
def independentCachedBranchMembers1995 : Finset ℕ := ([1644,1708,1748,1752,2652,2716,2788,2792,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1995 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1995 4 (fun x => (if x<2788 then (if x<1752 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2652 then 1 else (if x<2716 then 0 else 1))) else (if x<3162 then (if x<2792 then 0 else (if x<3118 then 1 else 2)) else (if x<3222 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1996 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792,3118,3162,3188,3192,3222,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1996 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1996 48 4
  · have he : independentCachedBranchMembers1996.erase 48=independentCachedBranchMembers1994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1994
  · have he : independentCachedBranchMembers1996.filter (independentCachedEdge 48)=independentCachedBranchMembers1995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1995
def independentCachedBranchMembers1997 : Finset ℕ := ([48,72,132,252,1590,1614,1708,1748,2652,2674,2758,2792,3162,3188,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1997 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1997 4 (fun x => (if x<2652 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1708 then (if x<1614 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3162 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3222 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1998 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792,3118,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1998 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1998 3226 4
  · have he : independentCachedBranchMembers1998.erase 3226=independentCachedBranchMembers1996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1996
  · have he : independentCachedBranchMembers1998.filter (independentCachedEdge 3226)=independentCachedBranchMembers1997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1997
def independentCachedBranchMembers1999 : Finset ℕ := ([48,72,132,252,1594,1644,1678,1752,2716,2738,2762,2788,3162,3188,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1999 4 (fun x => (if x<2716 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1678 then (if x<1644 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3162 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3222 then (if x<3188 then 3 else 3) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2000 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792,3118,3158,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2000 3158 4
  · have he : independentCachedBranchMembers2000.erase 3158=independentCachedBranchMembers1998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1998
  · have he : independentCachedBranchMembers2000.filter (independentCachedEdge 3158)=independentCachedBranchMembers1999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1999
def independentCachedBranchMembers2001 : Finset ℕ := ([48,252,1590,1594,1644,1708,2674,2738,2788,2792,3118,3188,3192,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2001 4 (fun x => (if x<2788 then (if x<1644 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1594 then 1 else 2)) else (if x<2674 then (if x<1708 then 1 else 2) else (if x<2738 then 2 else 1))) else (if x<3192 then (if x<3118 then (if x<2792 then 2 else 1) else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2002 : Finset ℕ := ([48,72,132,222,252,1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792,3118,3158,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2002 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2002 222 4
  · have he : independentCachedBranchMembers2002.erase 222=independentCachedBranchMembers2000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2000
  · have he : independentCachedBranchMembers2002.filter (independentCachedEdge 222)=independentCachedBranchMembers2001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2001
def independentCachedBranchMembers2003 : Finset ℕ := ([48,252,1614,1678,1748,1752,2652,2716,2758,2762,3118,3188,3192,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2003 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2003 4 (fun x => (if x<2758 then (if x<1748 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1678 then 1 else 2)) else (if x<2652 then (if x<1752 then 1 else 2) else (if x<2716 then 1 else 2))) else (if x<3192 then (if x<3118 then (if x<2762 then 1 else 2) else (if x<3188 then 3 else 0)) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2004 : Finset ℕ := ([18,48,72,132,222,252,1590,1594,1614,1644,1678,1708,1748,1752,2652,2674,2716,2738,2758,2762,2788,2792,3118,3158,3162,3188,3192,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2004 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2004 18 4
  · have he : independentCachedBranchMembers2004.erase 18=independentCachedBranchMembers2002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2002
  · have he : independentCachedBranchMembers2004.filter (independentCachedEdge 18)=independentCachedBranchMembers2003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2003
def independentCachedBranchMembers2005 : Finset ℕ := ([18,48,72,132,222,252,1590,1594,1596,1614,1642,1644,1678,1702,1708,1746,1748,1752,1776,2606,2646,2650,2652,2674,2680,2710,2714,2716,2738,2740,2758,2762,2764,2786,2788,2792,3118,3158,3162,3164,3186,3188,3192,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2005 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2005 2786 5
  · have he : independentCachedBranchMembers2005.erase 2786=independentCachedBranchMembers1991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1991
  · have he : independentCachedBranchMembers2005.filter (independentCachedEdge 2786)=independentCachedBranchMembers2004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2004
def independentCachedBranchMembers2006 : Finset ℕ := ([12,18,48,72,132,192,222,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2006 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2006 1582 6
  · have he : independentCachedBranchMembers2006.erase 1582=independentCachedBranchMembers1910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1910
  · have he : independentCachedBranchMembers2006.filter (independentCachedEdge 1582)=independentCachedBranchMembers2005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2005
def independentCachedBranchMembers2007 : Finset ℕ := ([132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2007 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2007 6 (fun x => (if x<2758 then (if x<2614 then (if x<1626 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1740 then (if x<1686 then 1 else 1) else (if x<1776 then 0 else 1))) else (if x<2680 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2730 then (if x<2716 then 1 else 0) else (if x<2740 then 2 else 1)))) else (if x<3214 then (if x<3130 then (if x<2776 then 3 else (if x<2788 then 3 else 0)) else (if x<3178 then (if x<3164 then 4 else 4) else (if x<3188 then 5 else 5))) else (if x<3256 then (if x<3244 then (if x<3238 then 4 else 5) else (if x<3250 then 0 else 2)) else (if x<3284 then (if x<3274 then 5 else 2) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2008 : Finset ℕ := ([1596,1776,2674,2716,2730,2758,2788,3130,3188,3214,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2008 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2008 5 (fun x => (if x<2788 then (if x<2716 then (if x<1776 then 0 else (if x<2674 then 0 else 1)) else (if x<2730 then 2 else (if x<2758 then 1 else 1))) else (if x<3214 then (if x<3130 then 2 else (if x<3188 then 1 else 0)) else (if x<3256 then (if x<3244 then 1 else 2) else (if x<3284 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2009 : Finset ℕ := ([72,132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2009 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2009 72 5
  · have he : independentCachedBranchMembers2009.erase 72=independentCachedBranchMembers2007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2007
  · have he : independentCachedBranchMembers2009.filter (independentCachedEdge 72)=independentCachedBranchMembers2008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2008
def independentCachedBranchMembers2010 : Finset ℕ := ([1626,1686,2668,2716,2730,2776,2788,3164,3178,3238,3244,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2010 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2010 5 (fun x => (if x<2788 then (if x<2716 then (if x<1686 then 0 else (if x<2668 then 0 else 1)) else (if x<2730 then 1 else (if x<2776 then 1 else 2))) else (if x<3238 then (if x<3164 then 2 else (if x<3178 then 1 else 0)) else (if x<3284 then (if x<3244 then 0 else 1) else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2011 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2011 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2011 48 5
  · have he : independentCachedBranchMembers2011.erase 48=independentCachedBranchMembers2009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2009
  · have he : independentCachedBranchMembers2011.filter (independentCachedEdge 48)=independentCachedBranchMembers2010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2010
def independentCachedBranchMembers2012 : Finset ℕ := ([48,72,132,252,1740,2668,2674,2758,2776,3130,3164,3178,3188,3214,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2012 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2012 5 (fun x => (if x<2776 then (if x<1740 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<2674 then (if x<2668 then 0 else 1) else (if x<2758 then 1 else 1))) else (if x<3188 then (if x<3164 then (if x<3130 then 1 else 2) else (if x<3178 then 2 else 3)) else (if x<3238 then (if x<3214 then 3 else 2) else (if x<3256 then 3 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2013 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2013 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2013 2770 5
  · have he : independentCachedBranchMembers2013.erase 2770=independentCachedBranchMembers2011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2011
  · have he : independentCachedBranchMembers2013.filter (independentCachedEdge 2770)=independentCachedBranchMembers2012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2012
def independentCachedBranchMembers2014 : Finset ℕ := ([1596,1626,1686,1740,1776,2614,2638,2668,2674,2716,2758,2776,2788,3178,3188,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2014 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2014 5 (fun x => (if x<2674 then (if x<1776 then (if x<1686 then (if x<1626 then 0 else 0) else (if x<1740 then 0 else 0)) else (if x<2638 then (if x<2614 then 0 else 1) else (if x<2668 then 1 else 2))) else (if x<2788 then (if x<2758 then (if x<2716 then 2 else 1) else (if x<2776 then 2 else 2)) else (if x<3188 then (if x<3178 then 1 else 3) else (if x<3238 then 3 else (if x<3256 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2015 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1740,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2015 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2015 2764 5
  · have he : independentCachedBranchMembers2015.erase 2764=independentCachedBranchMembers2013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2013
  · have he : independentCachedBranchMembers2015.filter (independentCachedEdge 2764)=independentCachedBranchMembers2014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2014
def independentCachedBranchMembers2016 : Finset ℕ := ([48,132,1626,1740,1776,2638,2668,2674,2730,2740,2758,2776,2788,3130,3178,3188,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound2016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2016 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2016 5 (fun x => (if x<2740 then (if x<1776 then (if x<1626 then (if x<132 then 0 else 0) else (if x<1740 then 1 else 0)) else (if x<2668 then (if x<2638 then 1 else 1) else (if x<2674 then 2 else (if x<2730 then 0 else 2)))) else (if x<3178 then (if x<2776 then (if x<2758 then 2 else 0) else (if x<2788 then 1 else (if x<3130 then 1 else 0))) else (if x<3214 then (if x<3188 then 2 else 2) else (if x<3244 then 0 else (if x<3250 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2017 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2017 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2017 1752 5
  · have he : independentCachedBranchMembers2017.erase 1752=independentCachedBranchMembers2015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2015
  · have he : independentCachedBranchMembers2017.filter (independentCachedEdge 1752)=independentCachedBranchMembers2016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2016
def independentCachedBranchMembers2018 : Finset ℕ := ([72,252,1596,1686,1740,2614,2668,2674,2716,2730,2740,2758,2776,3164,3178,3188,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2018 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2018 5 (fun x => (if x<2730 then (if x<1740 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2668 then (if x<2614 then 0 else 1) else (if x<2674 then 0 else (if x<2716 then 2 else 1)))) else (if x<3178 then (if x<2758 then (if x<2740 then 2 else 2) else (if x<2776 then 1 else (if x<3164 then 0 else 0))) else (if x<3244 then (if x<3188 then 2 else 2) else (if x<3250 then 2 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2019 : Finset ℕ := ([48,72,132,252,1596,1626,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2019 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2019 1734 5
  · have he : independentCachedBranchMembers2019.erase 1734=independentCachedBranchMembers2017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2017
  · have he : independentCachedBranchMembers2019.filter (independentCachedEdge 1734)=independentCachedBranchMembers2018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2018
def independentCachedBranchMembers2020 : Finset ℕ := ([72,252,1626,1740,1776,2638,2668,2674,2730,2740,2758,2776,2788,3164,3238,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2020 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2020 5 (fun x => (if x<2740 then (if x<1776 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1740 then 1 else 0)) else (if x<2668 then (if x<2638 then 1 else 1) else (if x<2674 then 0 else (if x<2730 then 1 else 2)))) else (if x<3238 then (if x<2776 then (if x<2758 then 2 else 2) else (if x<2788 then 0 else (if x<3164 then 1 else 0))) else (if x<3274 then (if x<3256 then 2 else 2) else (if x<3284 then 2 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2021 : Finset ℕ := ([48,72,132,252,1596,1626,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2021 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2021 1650 5
  · have he : independentCachedBranchMembers2021.erase 1650=independentCachedBranchMembers2019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2019
  · have he : independentCachedBranchMembers2021.filter (independentCachedEdge 1650)=independentCachedBranchMembers2020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2020
def independentCachedBranchMembers2022 : Finset ℕ := ([48,132,1596,1686,1740,2614,2668,2674,2716,2730,2740,2758,2776,3130,3214,3238,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2022 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2022 5 (fun x => (if x<2730 then (if x<1740 then (if x<1596 then (if x<132 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2668 then (if x<2614 then 0 else 1) else (if x<2674 then 1 else (if x<2716 then 0 else 1)))) else (if x<3214 then (if x<2758 then (if x<2740 then 2 else 2) else (if x<2776 then 0 else (if x<3130 then 2 else 0))) else (if x<3256 then (if x<3238 then 0 else 2) else (if x<3274 then 2 else (if x<3284 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2023 : Finset ℕ := ([48,72,132,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2023 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2023 1644 5
  · have he : independentCachedBranchMembers2023.erase 1644=independentCachedBranchMembers2021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2021
  · have he : independentCachedBranchMembers2023.filter (independentCachedEdge 1644)=independentCachedBranchMembers2022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2022
def independentCachedBranchMembers2024 : Finset ℕ := ([48,252,1596,1644,1650,1776,2614,2668,2674,2680,2730,2740,2788,3130,3178,3188,3238,3244,3250,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2024 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2024 5 (fun x => (if x<2730 then (if x<1776 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<2668 then (if x<2614 then 0 else 2) else (if x<2674 then 2 else (if x<2680 then 3 else 0)))) else (if x<3188 then (if x<2788 then (if x<2740 then 2 else 0) else (if x<3130 then 3 else (if x<3178 then 3 else 1))) else (if x<3250 then (if x<3238 then 0 else (if x<3244 then 4 else 1)) else (if x<3256 then 1 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2025 : Finset ℕ := ([48,72,132,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2025 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2025 222 5
  · have he : independentCachedBranchMembers2025.erase 222=independentCachedBranchMembers2023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2023
  · have he : independentCachedBranchMembers2025.filter (independentCachedEdge 222)=independentCachedBranchMembers2024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2024
def independentCachedBranchMembers2026 : Finset ℕ := ([72,132,1626,1644,1650,1686,2638,2668,2674,2680,2716,2730,2740,3164,3178,3188,3214,3238,3244,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2026 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2026 5 (fun x => (if x<2716 then (if x<1686 then (if x<1626 then (if x<132 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<2668 then (if x<2638 then 0 else 2) else (if x<2674 then 3 else (if x<2680 then 2 else 0)))) else (if x<3188 then (if x<2740 then (if x<2730 then 3 else 2) else (if x<3164 then 0 else (if x<3178 then 3 else 0))) else (if x<3244 then (if x<3214 then 1 else (if x<3238 then 2 else 0)) else (if x<3250 then 1 else (if x<3256 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2027 : Finset ℕ := ([48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2027 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2027 192 5
  · have he : independentCachedBranchMembers2027.erase 192=independentCachedBranchMembers2025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2025
  · have he : independentCachedBranchMembers2027.filter (independentCachedEdge 192)=independentCachedBranchMembers2026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2026
def independentCachedBranchMembers2028 : Finset ℕ := ([48,252,1596,1734,1752,1776,2638,2680,2716,2730,2740,2758,2776,3164,3178,3188,3214,3238,3256,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2028 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2028 5 (fun x => (if x<2740 then (if x<1776 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1734 then 0 else (if x<1752 then 1 else 1))) else (if x<2680 then (if x<2638 then 0 else 2) else (if x<2716 then 0 else (if x<2730 then 2 else 2)))) else (if x<3188 then (if x<2776 then (if x<2758 then 0 else 3) else (if x<3164 then 3 else (if x<3178 then 2 else 2))) else (if x<3256 then (if x<3214 then 0 else (if x<3238 then 2 else 1)) else (if x<3274 then 0 else (if x<3284 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2029 : Finset ℕ := ([18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2029 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2029 18 5
  · have he : independentCachedBranchMembers2029.erase 18=independentCachedBranchMembers2027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2027
  · have he : independentCachedBranchMembers2029.filter (independentCachedEdge 18)=independentCachedBranchMembers2028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2028
def independentCachedBranchMembers2030 : Finset ℕ := ([72,132,1626,1686,1734,1752,2614,2680,2730,2740,2758,2776,2788,3130,3178,3188,3238,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2030 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2030 5 (fun x => (if x<2758 then (if x<1752 then (if x<1626 then (if x<132 then 0 else 0) else (if x<1686 then 0 else (if x<1734 then 0 else 1))) else (if x<2680 then (if x<2614 then 1 else 2) else (if x<2730 then 0 else (if x<2740 then 2 else 0)))) else (if x<3188 then (if x<2788 then (if x<2776 then 2 else 3) else (if x<3130 then 3 else (if x<3178 then 2 else 0))) else (if x<3274 then (if x<3238 then 4 else (if x<3256 then 0 else 1)) else (if x<3284 then 1 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2031 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2031 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2031 12 5
  · have he : independentCachedBranchMembers2031.erase 12=independentCachedBranchMembers2029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2029
  · have he : independentCachedBranchMembers2031.filter (independentCachedEdge 12)=independentCachedBranchMembers2030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2030
def independentCachedBranchMembers2032 : Finset ℕ := ([18,72,132,222,252,1626,1644,1686,1740,1752,2614,2638,2668,2680,2740,2764,2776,3164,3178,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2032 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2032 5 (fun x => (if x<2638 then (if x<1626 then (if x<132 then (if x<72 then 0 else 0) else (if x<222 then 0 else (if x<252 then 0 else 1))) else (if x<1740 then (if x<1644 then 0 else (if x<1686 then 1 else 0)) else (if x<1752 then 0 else (if x<2614 then 1 else 2)))) else (if x<3164 then (if x<2740 then (if x<2668 then 2 else (if x<2680 then 3 else 1)) else (if x<2764 then 3 else (if x<2776 then 1 else 3))) else (if x<3250 then (if x<3178 then 1 else (if x<3238 then 4 else 4)) else (if x<3274 then 2 else (if x<3304 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2033 : Finset ℕ := ([18,222,1626,1644,1686,1752,2668,2776,3164,3178,3238,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2033 4 (fun x => (if x<2668 then (if x<1644 then (if x<222 then 0 else (if x<1626 then 0 else 0)) else (if x<1686 then 1 else (if x<1752 then 0 else 1))) else (if x<3178 then (if x<2776 then 2 else (if x<3164 then 2 else 1)) else (if x<3238 then 3 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2034 : Finset ℕ := ([18,48,72,132,222,252,1626,1644,1686,1740,1752,2614,2638,2668,2680,2740,2764,2776,3164,3178,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2034 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2034 48 4
  · have he : independentCachedBranchMembers2034.erase 48=independentCachedBranchMembers2032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2032
  · have he : independentCachedBranchMembers2034.filter (independentCachedEdge 48)=independentCachedBranchMembers2033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2033
def independentCachedBranchMembers2035 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2035 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2035 3298 5
  · have he : independentCachedBranchMembers2035.erase 3298=independentCachedBranchMembers2031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2031
  · have he : independentCachedBranchMembers2035.filter (independentCachedEdge 3298)=independentCachedBranchMembers2034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2034
def independentCachedBranchMembers2036 : Finset ℕ := ([12,48,132,192,252,1596,1650,1734,1740,1776,2614,2638,2674,2680,2740,2758,2764,3130,3188,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2036 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2036 5 (fun x => (if x<2638 then (if x<1596 then (if x<132 then (if x<48 then 0 else 0) else (if x<192 then 1 else (if x<252 then 0 else 0))) else (if x<1740 then (if x<1650 then 0 else (if x<1734 then 1 else 1)) else (if x<1776 then 0 else (if x<2614 then 0 else 2)))) else (if x<3130 then (if x<2740 then (if x<2674 then 2 else (if x<2680 then 3 else 1)) else (if x<2758 then 3 else (if x<2764 then 3 else 1))) else (if x<3250 then (if x<3188 then 1 else (if x<3214 then 4 else 1)) else (if x<3256 then 2 else (if x<3274 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2037 : Finset ℕ := ([12,192,1596,1650,1734,1776,2674,2758,3130,3188,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2037 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2037 4 (fun x => (if x<2674 then (if x<1650 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<1734 then 1 else (if x<1776 then 1 else 0))) else (if x<3188 then (if x<2758 then 2 else (if x<3130 then 2 else 1)) else (if x<3214 then 3 else (if x<3256 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2038 : Finset ℕ := ([12,48,72,132,192,252,1596,1650,1734,1740,1776,2614,2638,2674,2680,2740,2758,2764,3130,3188,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2038 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2038 72 4
  · have he : independentCachedBranchMembers2038.erase 72=independentCachedBranchMembers2036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2036
  · have he : independentCachedBranchMembers2038.filter (independentCachedEdge 72)=independentCachedBranchMembers2037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2037
def independentCachedBranchMembers2039 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2039 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2039 3226 5
  · have he : independentCachedBranchMembers2039.erase 3226=independentCachedBranchMembers2035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2035
  · have he : independentCachedBranchMembers2039.filter (independentCachedEdge 3226)=independentCachedBranchMembers2038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2038
def independentCachedBranchMembers2040 : Finset ℕ := ([12,48,72,192,252,1596,1644,1740,1752,1776,2668,2680,2716,2740,2764,2776,2788,3164,3188,3244,3256,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2040 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2040 5 (fun x => (if x<2680 then (if x<1596 then (if x<72 then (if x<48 then 0 else 0) else (if x<192 then 1 else (if x<252 then 0 else 0))) else (if x<1752 then (if x<1644 then 0 else (if x<1740 then 1 else 0)) else (if x<1776 then 1 else (if x<2668 then 0 else 2)))) else (if x<3164 then (if x<2764 then (if x<2716 then 1 else (if x<2740 then 2 else 3)) else (if x<2776 then 1 else (if x<2788 then 3 else 4))) else (if x<3256 then (if x<3188 then 1 else (if x<3244 then 4 else 2)) else (if x<3284 then 3 else (if x<3304 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2041 : Finset ℕ := ([12,192,1596,1644,1752,1776,2668,2776,3164,3188,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2041 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2041 4 (fun x => (if x<2668 then (if x<1644 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<1752 then 1 else (if x<1776 then 1 else 0))) else (if x<3188 then (if x<2776 then 2 else (if x<3164 then 2 else 1)) else (if x<3256 then 3 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2042 : Finset ℕ := ([12,48,72,132,192,252,1596,1644,1740,1752,1776,2668,2680,2716,2740,2764,2776,2788,3164,3188,3244,3256,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2042 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2042 132 4
  · have he : independentCachedBranchMembers2042.erase 132=independentCachedBranchMembers2040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2040
  · have he : independentCachedBranchMembers2042.filter (independentCachedEdge 132)=independentCachedBranchMembers2041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2041
def independentCachedBranchMembers2043 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2043 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2043 3158 5
  · have he : independentCachedBranchMembers2043.erase 3158=independentCachedBranchMembers2039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2039
  · have he : independentCachedBranchMembers2043.filter (independentCachedEdge 3158)=independentCachedBranchMembers2042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2042
def independentCachedBranchMembers2044 : Finset ℕ := ([18,48,72,132,222,1626,1650,1686,1734,1740,2674,2680,2716,2740,2758,2764,2788,3130,3178,3214,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2044 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2044 5 (fun x => (if x<2680 then (if x<1626 then (if x<72 then (if x<48 then 0 else 1) else (if x<132 then 0 else (if x<222 then 0 else 0))) else (if x<1734 then (if x<1650 then 0 else (if x<1686 then 1 else 0)) else (if x<1740 then 1 else (if x<2674 then 0 else 2)))) else (if x<3130 then (if x<2758 then (if x<2716 then 1 else (if x<2740 then 3 else 2)) else (if x<2764 then 2 else (if x<2788 then 1 else 3))) else (if x<3238 then (if x<3178 then 1 else (if x<3214 then 4 else 1)) else (if x<3244 then 4 else (if x<3284 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2045 : Finset ℕ := ([18,222,1626,1650,1686,1734,2674,2758,3130,3178,3214,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2045 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2045 4 (fun x => (if x<2674 then (if x<1650 then (if x<222 then 0 else (if x<1626 then 0 else 0)) else (if x<1686 then 1 else (if x<1734 then 0 else 1))) else (if x<3178 then (if x<2758 then 2 else (if x<3130 then 2 else 1)) else (if x<3214 then 3 else (if x<3238 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2046 : Finset ℕ := ([18,48,72,132,222,252,1626,1650,1686,1734,1740,2674,2680,2716,2740,2758,2764,2788,3130,3178,3214,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2046 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2046 252 4
  · have he : independentCachedBranchMembers2046.erase 252=independentCachedBranchMembers2044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2044
  · have he : independentCachedBranchMembers2046.filter (independentCachedEdge 252)=independentCachedBranchMembers2045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2045
def independentCachedBranchMembers2047 : Finset ℕ := ([12,18,48,72,132,192,222,252,1596,1626,1644,1650,1686,1734,1740,1752,1776,2614,2638,2668,2674,2680,2716,2730,2740,2758,2764,2770,2776,2788,3118,3130,3158,3164,3178,3188,3214,3226,3238,3244,3250,3256,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2047 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2047 3118 5
  · have he : independentCachedBranchMembers2047.erase 3118=independentCachedBranchMembers2043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2043
  · have he : independentCachedBranchMembers2047.filter (independentCachedEdge 3118)=independentCachedBranchMembers2046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2046
end EntropyDesigns.QuadraticRefinement
