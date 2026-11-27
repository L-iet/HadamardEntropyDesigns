/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch97
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5920 : Finset ℕ := ([1590,1596,1614,1652,1686,1692,1702,1708,1748,1764,2606,2646,2652,2668,2702,2740,2758,3118,3158,3164,3174,3214,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5920 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5920 1764 4
  · have he : independentCachedBranchMembers5920.erase 1764=independentCachedBranchMembers5918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5918
  · have he : independentCachedBranchMembers5920.filter (independentCachedEdge 1764)=independentCachedBranchMembers5919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5919
def independentCachedBranchMembers5921 : Finset ℕ := ([250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5921 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5921 250 5
  · have he : independentCachedBranchMembers5921.erase 250=independentCachedBranchMembers5915 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5915
  · have he : independentCachedBranchMembers5921.filter (independentCachedEdge 250)=independentCachedBranchMembers5920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5920
def independentCachedBranchMembers5922 : Finset ℕ := ([1590,1614,1626,1642,1692,1708,1720,1748,1764,1776,2606,2618,2646,2674,2740,2776,2792,3118,3130,3158,3174,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5922 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5922 5 (fun x => (if x<2646 then (if x<1720 then (if x<1642 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<1692 then 2 else (if x<1708 then 0 else 2))) else (if x<1776 then (if x<1748 then 1 else (if x<1764 then 1 else 0)) else (if x<2606 then 2 else (if x<2618 then 2 else 1)))) else (if x<3130 then (if x<2776 then (if x<2674 then 1 else (if x<2740 then 2 else 0)) else (if x<2792 then 1 else (if x<3118 then 2 else 3))) else (if x<3252 then (if x<3158 then 4 else (if x<3174 then 3 else 4)) else (if x<3276 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5923 : Finset ℕ := ([130,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5923 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5923 130 5
  · have he : independentCachedBranchMembers5923.erase 130=independentCachedBranchMembers5921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5921
  · have he : independentCachedBranchMembers5923.filter (independentCachedEdge 130)=independentCachedBranchMembers5922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5922
def independentCachedBranchMembers5924 : Finset ℕ := ([1590,1596,1614,1642,1686,1692,1714,1720,1738,1764,2618,2668,2714,2740,2758,2786,2792,3130,3174,3226,3252,3276,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5924 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5924 5 (fun x => (if x<2714 then (if x<1714 then (if x<1642 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1686 then 1 else (if x<1692 then 2 else 0))) else (if x<1764 then (if x<1720 then 1 else (if x<1738 then 2 else 2)) else (if x<2618 then 0 else (if x<2668 then 1 else 1)))) else (if x<3174 then (if x<2786 then (if x<2740 then 2 else (if x<2758 then 0 else 2)) else (if x<2792 then 1 else (if x<3130 then 2 else 3))) else (if x<3276 then (if x<3226 then 3 else (if x<3252 then 4 else 3)) else (if x<3298 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5925 : Finset ℕ := ([80,130,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5925 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5925 80 5
  · have he : independentCachedBranchMembers5925.erase 80=independentCachedBranchMembers5923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5923
  · have he : independentCachedBranchMembers5925.filter (independentCachedEdge 80)=independentCachedBranchMembers5924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5924
def independentCachedBranchMembers5926 : Finset ℕ := ([1590,1614,1626,1652,1692,1702,1714,1738,1764,1776,2652,2674,2702,2714,2740,2776,2786,3164,3174,3214,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5926 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5926 5 (fun x => (if x<2702 then (if x<1714 then (if x<1652 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 0 else 2))) else (if x<1776 then (if x<1738 then 1 else (if x<1764 then 2 else 0)) else (if x<2652 then 2 else (if x<2674 then 1 else 1)))) else (if x<3174 then (if x<2776 then (if x<2714 then 2 else (if x<2740 then 1 else 0)) else (if x<2786 then 2 else (if x<3164 then 2 else 3))) else (if x<3252 then (if x<3214 then 3 else (if x<3226 then 3 else 4)) else (if x<3276 then 3 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5927 : Finset ℕ := ([40,80,130,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5927 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5927 40 5
  · have he : independentCachedBranchMembers5927.erase 40=independentCachedBranchMembers5925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5925
  · have he : independentCachedBranchMembers5927.filter (independentCachedEdge 40)=independentCachedBranchMembers5926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5926
def independentCachedBranchMembers5928 : Finset ℕ := ([1596,1626,1652,1686,1714,1720,1748,2652,2674,2714,2740,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5928 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5928 5 (fun x => (if x<2714 then (if x<1714 then (if x<1652 then (if x<1626 then 0 else 0) else (if x<1686 then 1 else 0)) else (if x<1748 then (if x<1720 then 1 else 2) else (if x<2652 then 2 else (if x<2674 then 1 else 1)))) else (if x<3164 then (if x<3130 then (if x<2740 then 1 else 0) else (if x<3158 then 2 else 2)) else (if x<3226 then (if x<3192 then 3 else 4) else (if x<3252 then 3 else (if x<3282 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5929 : Finset ℕ := ([1596,1652,1686,1714,2652,2714,3130,3158,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5929 4 (fun x => (if x<2652 then (if x<1686 then (if x<1652 then 0 else 1) else (if x<1714 then 0 else 1)) else (if x<3130 then (if x<2714 then 1 else 1) else (if x<3158 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5930 : Finset ℕ := ([1596,1626,1652,1686,1714,1720,1748,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5930 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5930 2776 4
  · have he : independentCachedBranchMembers5930.erase 2776=independentCachedBranchMembers5928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5928
  · have he : independentCachedBranchMembers5930.filter (independentCachedEdge 2776)=independentCachedBranchMembers5929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5929
def independentCachedBranchMembers5931 : Finset ℕ := ([1596,1714,2652,2674,3130,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5931 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5931 4 (fun x => (if x<3130 then (if x<2652 then (if x<1714 then 0 else 0) else (if x<2674 then 0 else 1)) else (if x<3192 then (if x<3158 then 1 else 1) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5932 : Finset ℕ := ([1596,1626,1652,1686,1714,1720,1748,2646,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5932 2646 4
  · have he : independentCachedBranchMembers5932.erase 2646=independentCachedBranchMembers5930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5930
  · have he : independentCachedBranchMembers5932.filter (independentCachedEdge 2646)=independentCachedBranchMembers5931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5931
def independentCachedBranchMembers5933 : Finset ℕ := ([1652,1686,2674,2714,3130,3158,3164,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5933 4 (fun x => (if x<3130 then (if x<2674 then (if x<1686 then 0 else 0) else (if x<2714 then 1 else 0)) else (if x<3164 then (if x<3158 then 1 else 1) else (if x<3252 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5934 : Finset ℕ := ([1596,1626,1652,1686,1714,1720,1748,2618,2646,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5934 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5934 2618 4
  · have he : independentCachedBranchMembers5934.erase 2618=independentCachedBranchMembers5932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5932
  · have he : independentCachedBranchMembers5934.filter (independentCachedEdge 2618)=independentCachedBranchMembers5933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5933
def independentCachedBranchMembers5935 : Finset ℕ := ([1596,1686,1720,1748,2618,2646,3130,3158,3192,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5935 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5935 4 (fun x => (if x<2646 then (if x<1720 then (if x<1686 then 0 else 0) else (if x<1748 then 1 else (if x<2618 then 1 else 1))) else (if x<3158 then (if x<3130 then 1 else 2) else (if x<3192 then 2 else (if x<3282 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5936 : Finset ℕ := ([1596,1626,1652,1686,1692,1714,1720,1748,2618,2646,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5936 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5936 1692 4
  · have he : independentCachedBranchMembers5936.erase 1692=independentCachedBranchMembers5934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5934
  · have he : independentCachedBranchMembers5936.filter (independentCachedEdge 1692)=independentCachedBranchMembers5935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5935
def independentCachedBranchMembers5937 : Finset ℕ := ([1596,1652,1686,1714,2652,2714,3164,3192,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5937 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5937 4 (fun x => (if x<2714 then (if x<1686 then (if x<1652 then 0 else 1) else (if x<1714 then 0 else (if x<2652 then 1 else 1))) else (if x<3192 then (if x<3164 then 1 else 2) else (if x<3226 then 0 else (if x<3282 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5938 : Finset ℕ := ([1590,1596,1626,1652,1686,1692,1714,1720,1748,2618,2646,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5938 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5938 1590 4
  · have he : independentCachedBranchMembers5938.erase 1590=independentCachedBranchMembers5936 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5936
  · have he : independentCachedBranchMembers5938.filter (independentCachedEdge 1590)=independentCachedBranchMembers5937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5937
def independentCachedBranchMembers5939 : Finset ℕ := ([1652,1714,1720,1748,2618,2646,2652,2714,3130,3158,3164,3226] : List ℕ).toFinset
theorem independentCachedBranchBound5939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5939 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5939 4 (fun x => (if x<2652 then (if x<1748 then (if x<1714 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2646 then 1 else 1))) else (if x<3158 then (if x<2714 then 0 else (if x<3130 then 0 else 2)) else (if x<3164 then 2 else (if x<3226 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5940 : Finset ℕ := ([1590,1596,1626,1652,1686,1692,1714,1720,1748,1776,2618,2646,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5940 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5940 1776 4
  · have he : independentCachedBranchMembers5940.erase 1776=independentCachedBranchMembers5938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5938
  · have he : independentCachedBranchMembers5940.filter (independentCachedEdge 1776)=independentCachedBranchMembers5939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5939
def independentCachedBranchMembers5941 : Finset ℕ := ([1590,1596,1652,1686,1692,1748,2646,2652,2740,3158,3164,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5941 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5941 4 (fun x => (if x<2646 then (if x<1686 then (if x<1596 then 0 else (if x<1652 then 1 else 2)) else (if x<1692 then 1 else (if x<1748 then 0 else 3))) else (if x<3158 then (if x<2652 then 2 else (if x<2740 then 3 else 0)) else (if x<3164 then 3 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5942 : Finset ℕ := ([250,1590,1596,1626,1652,1686,1692,1714,1720,1748,1776,2618,2646,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5942 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5942 250 4
  · have he : independentCachedBranchMembers5942.erase 250=independentCachedBranchMembers5940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5940
  · have he : independentCachedBranchMembers5942.filter (independentCachedEdge 250)=independentCachedBranchMembers5941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5941
def independentCachedBranchMembers5943 : Finset ℕ := ([1590,1596,1686,1692,1714,1720,2618,2714,2740,3130,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5943 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5943 4 (fun x => (if x<2618 then (if x<1692 then (if x<1596 then 0 else (if x<1686 then 1 else 1)) else (if x<1714 then 0 else (if x<1720 then 2 else 3))) else (if x<3130 then (if x<2714 then 2 else (if x<2740 then 3 else 0)) else (if x<3226 then 3 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5944 : Finset ℕ := ([80,250,1590,1596,1626,1652,1686,1692,1714,1720,1748,1776,2618,2646,2652,2674,2714,2740,2776,3130,3158,3164,3192,3226,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5944 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5944 80 4
  · have he : independentCachedBranchMembers5944.erase 80=independentCachedBranchMembers5942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5942
  · have he : independentCachedBranchMembers5944.filter (independentCachedEdge 80)=independentCachedBranchMembers5943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5943
def independentCachedBranchMembers5945 : Finset ℕ := ([40,80,130,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5945 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5945 238 5
  · have he : independentCachedBranchMembers5945.erase 238=independentCachedBranchMembers5927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5927
  · have he : independentCachedBranchMembers5945.filter (independentCachedEdge 238)=independentCachedBranchMembers5944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5944
def independentCachedBranchMembers5946 : Finset ℕ := ([1596,1614,1626,1642,1702,1714,1748,1764,1776,2606,2618,2652,2668,2740,2758,2786,3118,3130,3164,3192,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5946 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5946 5 (fun x => (if x<2652 then (if x<1714 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1642 then 1 else (if x<1702 then 2 else 0))) else (if x<1776 then (if x<1748 then 1 else (if x<1764 then 0 else 2)) else (if x<2606 then 3 else (if x<2618 then 0 else 1)))) else (if x<3130 then (if x<2758 then (if x<2668 then 0 else (if x<2740 then 2 else 0)) else (if x<2786 then 0 else (if x<3118 then 2 else 3))) else (if x<3252 then (if x<3164 then 4 else (if x<3192 then 4 else 3)) else (if x<3282 then 3 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5947 : Finset ℕ := ([1642,1702,1714,1748,2606,2618,2652,2786,3118,3130,3164,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5947 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5947 4 (fun x => (if x<2652 then (if x<1748 then (if x<1702 then 0 else (if x<1714 then 0 else 1)) else (if x<2606 then 1 else (if x<2618 then 0 else 1))) else (if x<3130 then (if x<2786 then 1 else (if x<3118 then 0 else 2)) else (if x<3164 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5948 : Finset ℕ := ([1596,1614,1626,1642,1686,1702,1714,1748,1764,1776,2606,2618,2652,2668,2740,2758,2786,3118,3130,3164,3192,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5948 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5948 1686 4
  · have he : independentCachedBranchMembers5948.erase 1686=independentCachedBranchMembers5946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5946
  · have he : independentCachedBranchMembers5948.filter (independentCachedEdge 1686)=independentCachedBranchMembers5947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5947
def independentCachedBranchMembers5949 : Finset ℕ := ([1626,1642,1748,1764,1776,2606,2618,2740,3118,3130,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5949 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5949 4 (fun x => (if x<2606 then (if x<1748 then (if x<1642 then 0 else 1) else (if x<1764 then 0 else (if x<1776 then 1 else 2))) else (if x<3118 then (if x<2618 then 2 else (if x<2740 then 0 else 0)) else (if x<3130 then 3 else (if x<3252 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5950 : Finset ℕ := ([1626,1642,1776,2618,3130] : List ℕ).toFinset
theorem independentCachedBranchBound5950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5950 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5950 3 (fun x => (if x<1776 then (if x<1642 then 0 else 1) else (if x<2618 then 0 else (if x<3130 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5951 : Finset ℕ := ([1614,1626,1642,1748,1764,1776,2606,2618,2740,3118,3130,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5951 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5951 1614 3
  · have he : independentCachedBranchMembers5951.erase 1614=independentCachedBranchMembers5949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5949
  · have he : independentCachedBranchMembers5951.filter (independentCachedEdge 1614)=independentCachedBranchMembers5950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5950
end EntropyDesigns.QuadraticRefinement
