/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch223
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9952 : Finset ℕ := ([12,144,1590,1614,1644,1708,1748,1776,2614,2638,2666,2668,2732,2800,3118,3158,3186,3188,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9952 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9952 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9952 5 (fun x => (if x<2668 then (if x<1708 then (if x<1590 then (if x<144 then 0 else 0) else (if x<1614 then 1 else (if x<1644 then 0 else 1))) else (if x<2614 then (if x<1748 then 2 else (if x<1776 then 1 else 2)) else (if x<2638 then 3 else (if x<2666 then 3 else 4)))) else (if x<3186 then (if x<2800 then (if x<2732 then 0 else 3) else (if x<3118 then 0 else (if x<3158 then 0 else 3))) else (if x<3252 then (if x<3188 then 2 else (if x<3250 then 1 else 0)) else (if x<3276 then 2 else (if x<3304 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9953 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2668,2674,2676,2710,2732,2738,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9953 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9953 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9953 3126 5
  · have he : independentCachedBranchMembers9953.erase 3126=independentCachedBranchMembers9951 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9951
  · have he : independentCachedBranchMembers9953.filter (independentCachedEdge 3126)=independentCachedBranchMembers9952 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9952
def independentCachedBranchMembers9954 : Finset ℕ := ([12,18,144,246,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2764,3118,3158,3180,3186,3250] : List ℕ).toFinset
theorem independentCachedBranchBound9954 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9954 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9954 5 (fun x => (if x<1776 then (if x<1650 then (if x<144 then (if x<18 then 0 else 0) else (if x<246 then 1 else (if x<1644 then 1 else 0))) else (if x<1714 then (if x<1686 then 0 else (if x<1708 then 1 else 2)) else (if x<1738 then 2 else (if x<1748 then 2 else 2)))) else (if x<2764 then (if x<2638 then (if x<2614 then 1 else 3) else (if x<2666 then 3 else (if x<2676 then 4 else 4))) else (if x<3180 then (if x<3118 then 0 else (if x<3158 then 3 else 3)) else (if x<3186 then 4 else (if x<3250 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9955 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9955 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9955 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9955 2762 5
  · have he : independentCachedBranchMembers9955.erase 2762=independentCachedBranchMembers9953 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9953
  · have he : independentCachedBranchMembers9955.filter (independentCachedEdge 2762)=independentCachedBranchMembers9954 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9954
def independentCachedBranchMembers9956 : Finset ℕ := ([12,48,72,144,1644,1714,1738,1776,2614,2638,2674,2676,2710,2732,3118,3158,3178,3180,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9956 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9956 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9956 5 (fun x => (if x<2676 then (if x<1714 then (if x<72 then (if x<48 then 0 else 0) else (if x<144 then 1 else (if x<1644 then 1 else 1))) else (if x<2614 then (if x<1738 then 0 else (if x<1776 then 2 else 2)) else (if x<2638 then 3 else (if x<2674 then 0 else 0)))) else (if x<3178 then (if x<2732 then (if x<2710 then 2 else 1) else (if x<3118 then 3 else (if x<3158 then 3 else 3))) else (if x<3250 then (if x<3180 then 1 else (if x<3214 then 4 else 2)) else (if x<3252 then 1 else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9957 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9957 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9957 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9957 2646 5
  · have he : independentCachedBranchMembers9957.erase 2646=independentCachedBranchMembers9955 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9955
  · have he : independentCachedBranchMembers9957.filter (independentCachedEdge 2646)=independentCachedBranchMembers9956 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9956
def independentCachedBranchMembers9958 : Finset ℕ := ([18,48,72,246,1650,1686,1714,1738,2614,2638,2666,2668,2732,2800,3118,3158,3186,3188,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9958 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9958 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9958 5 (fun x => (if x<2668 then (if x<1686 then (if x<72 then (if x<48 then 0 else 1) else (if x<246 then 0 else (if x<1650 then 1 else 1))) else (if x<2614 then (if x<1714 then 0 else (if x<1738 then 2 else 2)) else (if x<2638 then 0 else (if x<2666 then 2 else 3)))) else (if x<3186 then (if x<2800 then (if x<2732 then 0 else 3) else (if x<3118 then 1 else (if x<3158 then 3 else 4))) else (if x<3252 then (if x<3188 then 3 else (if x<3250 then 1 else 0)) else (if x<3276 then 2 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9959 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9959 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9959 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9959 2606 5
  · have he : independentCachedBranchMembers9959.erase 2606=independentCachedBranchMembers9957 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9957
  · have he : independentCachedBranchMembers9959.filter (independentCachedEdge 2606)=independentCachedBranchMembers9958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9958
def independentCachedBranchMembers9960 : Finset ℕ := ([48,72,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2764,3126,3150,3178,3188,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9960 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9960 5 (fun x => (if x<2666 then (if x<1714 then (if x<1650 then (if x<72 then 0 else (if x<1644 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 2 else 2))) else (if x<1776 then (if x<1738 then 0 else (if x<1748 then 0 else 1)) else (if x<2614 then 2 else (if x<2638 then 0 else 0)))) else (if x<3188 then (if x<3126 then (if x<2676 then 1 else (if x<2764 then 1 else 1)) else (if x<3150 then 3 else (if x<3178 then 3 else 4))) else (if x<3276 then (if x<3214 then 4 else (if x<3252 then 2 else 0)) else (if x<3282 then 0 else (if x<3304 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9961 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1746,1748,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9961 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9961 1746 5
  · have he : independentCachedBranchMembers9961.erase 1746=independentCachedBranchMembers9959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9959
  · have he : independentCachedBranchMembers9961.filter (independentCachedEdge 1746)=independentCachedBranchMembers9960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9960
def independentCachedBranchMembers9962 : Finset ℕ := ([144,246,1590,1614,1644,1650,1708,1714,1738,1748,2606,2646,2666,2676,2710,2764,2800,3118,3158,3178,3188,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9962 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9962 5 (fun x => (if x<2666 then (if x<1708 then (if x<1614 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1748 then (if x<1714 then 1 else (if x<1738 then 0 else 2)) else (if x<2606 then 0 else (if x<2646 then 1 else 1)))) else (if x<3158 then (if x<2764 then (if x<2676 then 2 else (if x<2710 then 2 else 0)) else (if x<2800 then 1 else (if x<3118 then 0 else 3))) else (if x<3252 then (if x<3178 then 3 else (if x<3188 then 4 else 4)) else (if x<3276 then 0 else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9963 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1740,1746,1748,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9963 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9963 1740 5
  · have he : independentCachedBranchMembers9963.erase 1740=independentCachedBranchMembers9961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9961
  · have he : independentCachedBranchMembers9963.filter (independentCachedEdge 1740)=independentCachedBranchMembers9962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9962
def independentCachedBranchMembers9964 : Finset ℕ := ([12,18,1590,1614,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2764,3118,3158,3180,3186,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9964 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9964 5 (fun x => (if x<2668 then (if x<1714 then (if x<1614 then (if x<18 then 0 else (if x<1590 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 2 else 0))) else (if x<1776 then (if x<1738 then 0 else (if x<1748 then 2 else 1)) else (if x<2606 then 2 else (if x<2646 then 1 else 1)))) else (if x<3186 then (if x<3118 then (if x<2674 then 0 else (if x<2764 then 0 else 1)) else (if x<3158 then 3 else (if x<3180 then 3 else 4))) else (if x<3276 then (if x<3214 then 4 else (if x<3252 then 2 else 2)) else (if x<3282 then 0 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9965 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1716,1738,1740,1746,1748,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9965 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9965 1716 5
  · have he : independentCachedBranchMembers9965.erase 1716=independentCachedBranchMembers9963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9963
  · have he : independentCachedBranchMembers9965.filter (independentCachedEdge 1716)=independentCachedBranchMembers9964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9964
def independentCachedBranchMembers9966 : Finset ℕ := ([12,18,48,72,144,246,1708,1714,1738,1748,2614,2638,2668,2674,2710,2764,2800,3126,3150,3180,3186,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9966 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9966 5 (fun x => (if x<2668 then (if x<1708 then (if x<72 then (if x<18 then 0 else (if x<48 then 0 else 1)) else (if x<144 then 1 else (if x<246 then 2 else 2))) else (if x<1748 then (if x<1714 then 0 else (if x<1738 then 0 else 1)) else (if x<2614 then 2 else (if x<2638 then 1 else 1)))) else (if x<3150 then (if x<2764 then (if x<2674 then 0 else (if x<2710 then 0 else 2)) else (if x<2800 then 3 else (if x<3126 then 2 else 3))) else (if x<3252 then (if x<3180 then 3 else (if x<3186 then 4 else 4)) else (if x<3276 then 1 else (if x<3282 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9967 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1706,1708,1714,1716,1738,1740,1746,1748,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9967 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9967 1706 5
  · have he : independentCachedBranchMembers9967.erase 1706=independentCachedBranchMembers9965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9965
  · have he : independentCachedBranchMembers9967.filter (independentCachedEdge 1706)=independentCachedBranchMembers9966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9966
def independentCachedBranchMembers9968 : Finset ℕ := ([12,48,1590,1644,1686,1706,1708,1738,1740,1776,2606,2638,2674,2676,2738,3118,3150,3186,3188,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9968 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9968 5 (fun x => (if x<2674 then (if x<1708 then (if x<1644 then (if x<48 then 0 else (if x<1590 then 0 else 1)) else (if x<1686 then 1 else (if x<1706 then 2 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1740 then 2 else 0)) else (if x<2606 then 0 else (if x<2638 then 1 else 0)))) else (if x<3188 then (if x<3118 then (if x<2676 then 0 else (if x<2738 then 1 else 1)) else (if x<3150 then 3 else (if x<3186 then 4 else 3))) else (if x<3252 then (if x<3214 then 4 else (if x<3250 then 0 else 0)) else (if x<3282 then 2 else (if x<3304 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9969 : Finset ℕ := ([12,1644,1706,1708,1738,1740,2606,2638,3118,3150,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9969 4 (fun x => (if x<2606 then (if x<1708 then (if x<1644 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1740 then 2 else 1))) else (if x<3150 then (if x<2638 then 0 else (if x<3118 then 3 else 3)) else (if x<3214 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9970 : Finset ℕ := ([12,48,246,1590,1644,1686,1706,1708,1738,1740,1776,2606,2638,2674,2676,2738,3118,3150,3186,3188,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9970 246 4
  · have he : independentCachedBranchMembers9970.erase 246=independentCachedBranchMembers9968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9968
  · have he : independentCachedBranchMembers9970.filter (independentCachedEdge 246)=independentCachedBranchMembers9969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9969
def independentCachedBranchMembers9971 : Finset ℕ := ([48,1590,1706,1708,1738,1740,2674,2676,3186,3188,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9971 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9971 4 (fun x => (if x<2674 then (if x<1708 then (if x<1590 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1740 then 2 else 1))) else (if x<3188 then (if x<2676 then 0 else (if x<3186 then 3 else 3)) else (if x<3214 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9972 : Finset ℕ := ([12,48,144,246,1590,1644,1686,1706,1708,1738,1740,1776,2606,2638,2674,2676,2738,3118,3150,3186,3188,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9972 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9972 144 4
  · have he : independentCachedBranchMembers9972.erase 144=independentCachedBranchMembers9970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9970
  · have he : independentCachedBranchMembers9972.filter (independentCachedEdge 144)=independentCachedBranchMembers9971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9971
def independentCachedBranchMembers9973 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9973 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9973 1768 5
  · have he : independentCachedBranchMembers9973.erase 1768=independentCachedBranchMembers9967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9967
  · have he : independentCachedBranchMembers9973.filter (independentCachedEdge 1768)=independentCachedBranchMembers9972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9972
def independentCachedBranchMembers9974 : Finset ℕ := ([18,72,1614,1650,1686,1706,1708,1738,1740,1776,2614,2646,2666,2668,2738,3126,3158,3178,3180,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9974 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9974 5 (fun x => (if x<2666 then (if x<1708 then (if x<1650 then (if x<72 then 0 else (if x<1614 then 0 else 1)) else (if x<1686 then 1 else (if x<1706 then 0 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1740 then 2 else 0)) else (if x<2614 then 2 else (if x<2646 then 0 else 1)))) else (if x<3180 then (if x<3126 then (if x<2668 then 1 else (if x<2738 then 0 else 1)) else (if x<3158 then 3 else (if x<3178 then 4 else 3))) else (if x<3252 then (if x<3214 then 4 else (if x<3250 then 2 else 0)) else (if x<3282 then 2 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9975 : Finset ℕ := ([72,1614,1706,1708,1738,1740,2666,2668,3178,3180,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9975 4 (fun x => (if x<2666 then (if x<1708 then (if x<1614 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1740 then 2 else 1))) else (if x<3180 then (if x<2668 then 0 else (if x<3178 then 3 else 3)) else (if x<3214 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9976 : Finset ℕ := ([18,72,246,1614,1650,1686,1706,1708,1738,1740,1776,2614,2646,2666,2668,2738,3126,3158,3178,3180,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9976 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9976 246 4
  · have he : independentCachedBranchMembers9976.erase 246=independentCachedBranchMembers9974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9974
  · have he : independentCachedBranchMembers9976.filter (independentCachedEdge 246)=independentCachedBranchMembers9975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9975
def independentCachedBranchMembers9977 : Finset ℕ := ([18,1650,1706,1708,1738,1740,2614,2646,3126,3158,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9977 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9977 4 (fun x => (if x<2614 then (if x<1708 then (if x<1650 then 0 else (if x<1706 then 0 else 1)) else (if x<1738 then 2 else (if x<1740 then 2 else 1))) else (if x<3158 then (if x<2646 then 0 else (if x<3126 then 3 else 3)) else (if x<3214 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9978 : Finset ℕ := ([18,72,144,246,1614,1650,1686,1706,1708,1738,1740,1776,2614,2646,2666,2668,2738,3126,3158,3178,3180,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9978 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9978 144 4
  · have he : independentCachedBranchMembers9978.erase 144=independentCachedBranchMembers9976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9976
  · have he : independentCachedBranchMembers9978.filter (independentCachedEdge 144)=independentCachedBranchMembers9977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9977
def independentCachedBranchMembers9979 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9979 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9979 1678 5
  · have he : independentCachedBranchMembers9979.erase 1678=independentCachedBranchMembers9973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9973
  · have he : independentCachedBranchMembers9979.filter (independentCachedEdge 1678)=independentCachedBranchMembers9978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9978
def independentCachedBranchMembers9980 : Finset ℕ := ([18,48,246,1590,1650,1714,1716,1746,1748,2614,2646,2674,2676,2710,2738,2800,3126,3158,3186,3188,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9980 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9980 5 (fun x => (if x<2674 then (if x<1714 then (if x<246 then (if x<48 then 0 else 1) else (if x<1590 then 0 else (if x<1650 then 0 else 1))) else (if x<1748 then (if x<1716 then 2 else (if x<1746 then 1 else 0)) else (if x<2614 then 2 else (if x<2646 then 1 else 0)))) else (if x<3158 then (if x<2738 then (if x<2676 then 3 else (if x<2710 then 4 else 2)) else (if x<2800 then 0 else (if x<3126 then 1 else 3))) else (if x<3250 then (if x<3186 then 4 else (if x<3188 then 0 else 1)) else (if x<3252 then 1 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9981 : Finset ℕ := ([18,1650,1714,1716,1746,1748,2614,2646,2710,2800,3126,3158] : List ℕ).toFinset
theorem independentCachedBranchBound9981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9981 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9981 4 (fun x => (if x<2614 then (if x<1716 then (if x<1650 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2800 then (if x<2646 then 0 else (if x<2710 then 3 else 1)) else (if x<3126 then 1 else (if x<3158 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9982 : Finset ℕ := ([18,48,246,1590,1650,1714,1716,1746,1748,1776,2614,2646,2674,2676,2710,2738,2800,3126,3158,3186,3188,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9982 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9982 1776 4
  · have he : independentCachedBranchMembers9982.erase 1776=independentCachedBranchMembers9980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9980
  · have he : independentCachedBranchMembers9982.filter (independentCachedEdge 1776)=independentCachedBranchMembers9981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9981
def independentCachedBranchMembers9983 : Finset ℕ := ([48,1590,1714,1716,1746,1748,2674,2676,2710,2800,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound9983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9983 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9983 4 (fun x => (if x<2674 then (if x<1716 then (if x<1590 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2800 then (if x<2676 then 0 else (if x<2710 then 3 else 1)) else (if x<3186 then 1 else (if x<3188 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
