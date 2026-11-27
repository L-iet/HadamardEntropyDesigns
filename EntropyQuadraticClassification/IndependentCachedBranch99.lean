/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch98
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5952 : Finset ℕ := ([130,1596,1614,1626,1642,1686,1702,1714,1748,1764,1776,2606,2618,2652,2668,2740,2758,2786,3118,3130,3164,3192,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5952 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5952 130 4
  · have he : independentCachedBranchMembers5952.erase 130=independentCachedBranchMembers5948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5948
  · have he : independentCachedBranchMembers5952.filter (independentCachedEdge 130)=independentCachedBranchMembers5951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5951
def independentCachedBranchMembers5953 : Finset ℕ := ([1614,1626,1702,1714,1764,1776,2652,2740,2786,3164,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5953 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5953 4 (fun x => (if x<2652 then (if x<1714 then (if x<1626 then 0 else (if x<1702 then 1 else 0)) else (if x<1764 then 1 else (if x<1776 then 2 else 3))) else (if x<3164 then (if x<2740 then 0 else (if x<2786 then 0 else 2)) else (if x<3252 then 1 else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5954 : Finset ℕ := ([40,130,1596,1614,1626,1642,1686,1702,1714,1748,1764,1776,2606,2618,2652,2668,2740,2758,2786,3118,3130,3164,3192,3252,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5954 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5954 40 4
  · have he : independentCachedBranchMembers5954.erase 40=independentCachedBranchMembers5952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5952
  · have he : independentCachedBranchMembers5954.filter (independentCachedEdge 40)=independentCachedBranchMembers5953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5953
def independentCachedBranchMembers5955 : Finset ℕ := ([40,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5955 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5955 136 5
  · have he : independentCachedBranchMembers5955.erase 136=independentCachedBranchMembers5945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5945
  · have he : independentCachedBranchMembers5955.filter (independentCachedEdge 136)=independentCachedBranchMembers5954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5954
def independentCachedBranchMembers5956 : Finset ℕ := ([1590,1596,1626,1642,1686,1692,1702,1708,1738,1776,2606,2674,2702,2740,2776,2786,2792,3118,3192,3214,3252,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5956 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5956 5 (fun x => (if x<2702 then (if x<1702 then (if x<1642 then (if x<1596 then 0 else (if x<1626 then 1 else 0)) else (if x<1686 then 1 else (if x<1692 then 2 else 0))) else (if x<1776 then (if x<1708 then 1 else (if x<1738 then 2 else 2)) else (if x<2606 then 0 else (if x<2674 then 1 else 0)))) else (if x<3192 then (if x<2786 then (if x<2740 then 2 else (if x<2776 then 0 else 0)) else (if x<2792 then 1 else (if x<3118 then 2 else 3))) else (if x<3282 then (if x<3214 then 3 else (if x<3252 then 4 else 3)) else (if x<3298 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5957 : Finset ℕ := ([1590,1596,1686,1692,1702,1708,2606,2702,2740,3118,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5957 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5957 4 (fun x => (if x<2606 then (if x<1692 then (if x<1596 then 0 else (if x<1686 then 1 else 1)) else (if x<1702 then 0 else (if x<1708 then 2 else 3))) else (if x<3118 then (if x<2702 then 2 else (if x<2740 then 3 else 0)) else (if x<3214 then 3 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5958 : Finset ℕ := ([250,1590,1596,1626,1642,1686,1692,1702,1708,1738,1776,2606,2674,2702,2740,2776,2786,2792,3118,3192,3214,3252,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5958 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5958 250 4
  · have he : independentCachedBranchMembers5958.erase 250=independentCachedBranchMembers5956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5956
  · have he : independentCachedBranchMembers5958.filter (independentCachedEdge 250)=independentCachedBranchMembers5957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5957
def independentCachedBranchMembers5959 : Finset ℕ := ([1596,1642,1686,1692,1738,2740,2786,2792,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5959 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5959 4 (fun x => (if x<2740 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1692 then 1 else (if x<1738 then 2 else 1))) else (if x<3252 then (if x<2786 then 0 else (if x<2792 then 0 else 1)) else (if x<3298 then 2 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5960 : Finset ℕ := ([1596,1686,1738,2786,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5960 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5960 3 (fun x => (if x<1738 then (if x<1686 then 0 else 0) else (if x<2786 then 1 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5961 : Finset ℕ := ([1590,1596,1642,1686,1692,1738,2740,2786,2792,3252,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5961 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5961 1590 3
  · have he : independentCachedBranchMembers5961.erase 1590=independentCachedBranchMembers5959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5959
  · have he : independentCachedBranchMembers5961.filter (independentCachedEdge 1590)=independentCachedBranchMembers5960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5960
def independentCachedBranchMembers5962 : Finset ℕ := ([80,250,1590,1596,1626,1642,1686,1692,1702,1708,1738,1776,2606,2674,2702,2740,2776,2786,2792,3118,3192,3214,3252,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5962 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5962 80 4
  · have he : independentCachedBranchMembers5962.erase 80=independentCachedBranchMembers5958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5958
  · have he : independentCachedBranchMembers5962.filter (independentCachedEdge 80)=independentCachedBranchMembers5961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5961
def independentCachedBranchMembers5963 : Finset ℕ := ([40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5963 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5963 68 5
  · have he : independentCachedBranchMembers5963.erase 68=independentCachedBranchMembers5955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5955
  · have he : independentCachedBranchMembers5963.filter (independentCachedEdge 68)=independentCachedBranchMembers5962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5962
def independentCachedBranchMembers5964 : Finset ℕ := ([1596,1614,1626,1652,1686,1708,1720,1738,1764,1776,2646,2668,2702,2714,2740,2758,2792,3158,3192,3214,3226,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5964 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5964 5 (fun x => (if x<2702 then (if x<1720 then (if x<1652 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 0 else 2))) else (if x<1776 then (if x<1738 then 1 else (if x<1764 then 2 else 0)) else (if x<2646 then 2 else (if x<2668 then 1 else 0)))) else (if x<3192 then (if x<2758 then (if x<2714 then 2 else (if x<2740 then 1 else 0)) else (if x<2792 then 0 else (if x<3158 then 2 else 3))) else (if x<3252 then (if x<3214 then 3 else (if x<3226 then 4 else 3)) else (if x<3282 then 3 else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5965 : Finset ℕ := ([1614,1626,1708,1720,1764,1776,2646,2740,2792,3158,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5965 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5965 4 (fun x => (if x<2646 then (if x<1720 then (if x<1626 then 0 else (if x<1708 then 1 else 0)) else (if x<1764 then 1 else (if x<1776 then 2 else 3))) else (if x<3158 then (if x<2740 then 0 else (if x<2792 then 0 else 2)) else (if x<3252 then 1 else (if x<3304 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5966 : Finset ℕ := ([130,1596,1614,1626,1652,1686,1708,1720,1738,1764,1776,2646,2668,2702,2714,2740,2758,2792,3158,3192,3214,3226,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5966 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5966 130 4
  · have he : independentCachedBranchMembers5966.erase 130=independentCachedBranchMembers5964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5964
  · have he : independentCachedBranchMembers5966.filter (independentCachedEdge 130)=independentCachedBranchMembers5965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5965
def independentCachedBranchMembers5967 : Finset ℕ := ([1626,1652,1738,1764,1776,2702,2714,2740,3214,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5967 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5967 4 (fun x => (if x<2702 then (if x<1738 then (if x<1652 then 0 else 0) else (if x<1764 then 1 else (if x<1776 then 1 else 2))) else (if x<3214 then (if x<2714 then 2 else (if x<2740 then 0 else 0)) else (if x<3226 then 3 else (if x<3252 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5968 : Finset ℕ := ([1626,1738,1776,2714,3226] : List ℕ).toFinset
theorem independentCachedBranchBound5968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5968 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5968 3 (fun x => (if x<1776 then (if x<1738 then 0 else 1) else (if x<2714 then 0 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5969 : Finset ℕ := ([1614,1626,1652,1738,1764,1776,2702,2714,2740,3214,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound5969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5969 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5969 1614 3
  · have he : independentCachedBranchMembers5969.erase 1614=independentCachedBranchMembers5967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5967
  · have he : independentCachedBranchMembers5969.filter (independentCachedEdge 1614)=independentCachedBranchMembers5968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5968
def independentCachedBranchMembers5970 : Finset ℕ := ([40,130,1596,1614,1626,1652,1686,1708,1720,1738,1764,1776,2646,2668,2702,2714,2740,2758,2792,3158,3192,3214,3226,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5970 40 4
  · have he : independentCachedBranchMembers5970.erase 40=independentCachedBranchMembers5966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5966
  · have he : independentCachedBranchMembers5970.filter (independentCachedEdge 40)=independentCachedBranchMembers5969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5969
def independentCachedBranchMembers5971 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5971 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5971 34 5
  · have he : independentCachedBranchMembers5971.erase 34=independentCachedBranchMembers5963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5963
  · have he : independentCachedBranchMembers5971.filter (independentCachedEdge 34)=independentCachedBranchMembers5970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5970
def independentCachedBranchMembers5972 : Finset ℕ := ([1596,1614,1642,1652,1686,1708,1714,1764,2618,2646,2668,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5972 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5972 5 (fun x => (if x<2730 then (if x<1714 then (if x<1652 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 0 else 1))) else (if x<2646 then (if x<1764 then 1 else (if x<2618 then 0 else 2)) else (if x<2668 then 2 else (if x<2702 then 0 else 2)))) else (if x<3164 then (if x<2776 then (if x<2740 then 1 else (if x<2758 then 0 else 0)) else (if x<2786 then 2 else (if x<3118 then 2 else 3))) else (if x<3226 then (if x<3174 then 3 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 3 else 4) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5973 : Finset ℕ := ([1596,1652,1686,1714,2618,2646,2740,2776,3164,3192,3226,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5973 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5973 4 (fun x => (if x<2740 then (if x<1714 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<2618 then 1 else (if x<2646 then 2 else 2))) else (if x<3192 then (if x<2776 then 0 else (if x<3164 then 2 else 1)) else (if x<3226 then 3 else (if x<3282 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5974 : Finset ℕ := ([238,1596,1614,1642,1652,1686,1708,1714,1764,2618,2646,2668,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5974 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5974 238 4
  · have he : independentCachedBranchMembers5974.erase 238=independentCachedBranchMembers5972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5972
  · have he : independentCachedBranchMembers5974.filter (independentCachedEdge 238)=independentCachedBranchMembers5973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5973
def independentCachedBranchMembers5975 : Finset ℕ := ([1614,1642,1708,1764,2618,2646,2740,2776,3118,3174,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5975 4 (fun x => (if x<2740 then (if x<1764 then (if x<1642 then 0 else (if x<1708 then 1 else 0)) else (if x<2618 then 1 else (if x<2646 then 1 else 0))) else (if x<3174 then (if x<2776 then 0 else (if x<3118 then 2 else 2)) else (if x<3276 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5976 : Finset ℕ := ([130,238,1596,1614,1642,1652,1686,1708,1714,1764,2618,2646,2668,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5976 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5976 130 4
  · have he : independentCachedBranchMembers5976.erase 130=independentCachedBranchMembers5974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5974
  · have he : independentCachedBranchMembers5976.filter (independentCachedEdge 130)=independentCachedBranchMembers5975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5975
def independentCachedBranchMembers5977 : Finset ℕ := ([1596,1642,1686,1708,2702,2740,2776,2786,3118,3192,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5977 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5977 4 (fun x => (if x<2776 then (if x<1708 then (if x<1642 then 0 else (if x<1686 then 0 else 1)) else (if x<2702 then 1 else (if x<2740 then 1 else 0))) else (if x<3192 then (if x<2786 then 2 else (if x<3118 then 0 else 2)) else (if x<3282 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5978 : Finset ℕ := ([68,130,238,1596,1614,1642,1652,1686,1708,1714,1764,2618,2646,2668,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5978 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5978 68 4
  · have he : independentCachedBranchMembers5978.erase 68=independentCachedBranchMembers5976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5976
  · have he : independentCachedBranchMembers5978.filter (independentCachedEdge 68)=independentCachedBranchMembers5977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5977
def independentCachedBranchMembers5979 : Finset ℕ := ([1614,1652,1714,1764,2702,2740,2776,2786,3164,3174,3226,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5979 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5979 4 (fun x => (if x<2776 then (if x<1764 then (if x<1652 then 0 else (if x<1714 then 0 else 1)) else (if x<2702 then 1 else (if x<2740 then 0 else 0))) else (if x<3174 then (if x<2786 then 2 else (if x<3164 then 1 else 2)) else (if x<3226 then 2 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5980 : Finset ℕ := ([40,68,130,238,1596,1614,1642,1652,1686,1708,1714,1764,2618,2646,2668,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5980 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5980 40 4
  · have he : independentCachedBranchMembers5980.erase 40=independentCachedBranchMembers5978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5978
  · have he : independentCachedBranchMembers5980.filter (independentCachedEdge 40)=independentCachedBranchMembers5979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5979
def independentCachedBranchMembers5981 : Finset ℕ := ([40,68,130,238,1596,1614,1686,1764,2618,2646,2702,2786,3118,3164,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5981 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5981 4 (fun x => (if x<2618 then (if x<1596 then (if x<130 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1686 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3226 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5982 : Finset ℕ := ([40,68,130,238,1596,1614,1642,1652,1686,1708,1714,1764,2618,2646,2668,2674,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5982 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5982 2674 4
  · have he : independentCachedBranchMembers5982.erase 2674=independentCachedBranchMembers5980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5980
  · have he : independentCachedBranchMembers5982.filter (independentCachedEdge 2674)=independentCachedBranchMembers5981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5981
def independentCachedBranchMembers5983 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5983 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5983 3288 5
  · have he : independentCachedBranchMembers5983.erase 3288=independentCachedBranchMembers5971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5971
  · have he : independentCachedBranchMembers5983.filter (independentCachedEdge 3288)=independentCachedBranchMembers5982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5982
end EntropyDesigns.QuadraticRefinement
