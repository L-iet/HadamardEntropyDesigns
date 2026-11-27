/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch224
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9984 : Finset ℕ := ([18,48,246,1590,1650,1686,1714,1716,1746,1748,1776,2614,2646,2674,2676,2710,2738,2800,3126,3158,3186,3188,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9984 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9984 1686 4
  · have he : independentCachedBranchMembers9984.erase 1686=independentCachedBranchMembers9982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9982
  · have he : independentCachedBranchMembers9984.filter (independentCachedEdge 1686)=independentCachedBranchMembers9983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9983
def independentCachedBranchMembers9985 : Finset ℕ := ([18,48,1590,1650,2614,2646,2674,2676,3126,3158,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound9985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9985 4 (fun x => (if x<2674 then (if x<1650 then (if x<48 then 0 else (if x<1590 then 1 else 0)) else (if x<2614 then 1 else (if x<2646 then 1 else 0))) else (if x<3158 then (if x<2676 then 2 else (if x<3126 then 3 else 2)) else (if x<3186 then 3 else (if x<3188 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9986 : Finset ℕ := ([18,48,144,246,1590,1650,1686,1714,1716,1746,1748,1776,2614,2646,2674,2676,2710,2738,2800,3126,3158,3186,3188,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9986 144 4
  · have he : independentCachedBranchMembers9986.erase 144=independentCachedBranchMembers9984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9984
  · have he : independentCachedBranchMembers9986.filter (independentCachedEdge 144)=independentCachedBranchMembers9985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9985
def independentCachedBranchMembers9987 : Finset ℕ := ([12,18,48,72,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9987 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9987 238 5
  · have he : independentCachedBranchMembers9987.erase 238=independentCachedBranchMembers9979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9979
  · have he : independentCachedBranchMembers9987.filter (independentCachedEdge 238)=independentCachedBranchMembers9986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9986
def independentCachedBranchMembers9988 : Finset ℕ := ([12,72,144,1614,1644,1714,1716,1746,1748,2606,2638,2666,2668,2710,2738,2800,3118,3150,3178,3180,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9988 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9988 5 (fun x => (if x<2666 then (if x<1714 then (if x<144 then (if x<72 then 0 else 1) else (if x<1614 then 0 else (if x<1644 then 0 else 1))) else (if x<1748 then (if x<1716 then 2 else (if x<1746 then 1 else 0)) else (if x<2606 then 2 else (if x<2638 then 0 else 1)))) else (if x<3150 then (if x<2738 then (if x<2668 then 3 else (if x<2710 then 4 else 1)) else (if x<2800 then 0 else (if x<3118 then 2 else 3))) else (if x<3250 then (if x<3178 then 4 else (if x<3180 then 1 else 0)) else (if x<3252 then 1 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9989 : Finset ℕ := ([72,1614,1714,1716,1746,1748,2666,2668,2710,2800,3178,3180] : List ℕ).toFinset
theorem independentCachedBranchBound9989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9989 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9989 4 (fun x => (if x<2666 then (if x<1716 then (if x<1614 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2800 then (if x<2668 then 0 else (if x<2710 then 3 else 1)) else (if x<3178 then 1 else (if x<3180 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9990 : Finset ℕ := ([12,72,144,1614,1644,1714,1716,1746,1748,1776,2606,2638,2666,2668,2710,2738,2800,3118,3150,3178,3180,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9990 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9990 1776 4
  · have he : independentCachedBranchMembers9990.erase 1776=independentCachedBranchMembers9988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9988
  · have he : independentCachedBranchMembers9990.filter (independentCachedEdge 1776)=independentCachedBranchMembers9989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9989
def independentCachedBranchMembers9991 : Finset ℕ := ([12,1644,1714,1716,1746,1748,2606,2638,2710,2800,3118,3150] : List ℕ).toFinset
theorem independentCachedBranchBound9991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9991 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9991 4 (fun x => (if x<2606 then (if x<1716 then (if x<1644 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2800 then (if x<2638 then 0 else (if x<2710 then 3 else 1)) else (if x<3118 then 1 else (if x<3150 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9992 : Finset ℕ := ([12,72,144,1614,1644,1686,1714,1716,1746,1748,1776,2606,2638,2666,2668,2710,2738,2800,3118,3150,3178,3180,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9992 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9992 1686 4
  · have he : independentCachedBranchMembers9992.erase 1686=independentCachedBranchMembers9990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9990
  · have he : independentCachedBranchMembers9992.filter (independentCachedEdge 1686)=independentCachedBranchMembers9991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9991
def independentCachedBranchMembers9993 : Finset ℕ := ([12,72,1614,1644,2606,2638,2666,2668,3118,3150,3178,3180] : List ℕ).toFinset
theorem independentCachedBranchBound9993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9993 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9993 4 (fun x => (if x<2666 then (if x<1644 then (if x<72 then 0 else (if x<1614 then 1 else 0)) else (if x<2606 then 1 else (if x<2638 then 0 else 1))) else (if x<3150 then (if x<2668 then 2 else (if x<3118 then 3 else 2)) else (if x<3178 then 3 else (if x<3180 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9994 : Finset ℕ := ([12,72,144,246,1614,1644,1686,1714,1716,1746,1748,1776,2606,2638,2666,2668,2710,2738,2800,3118,3150,3178,3180,3250,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9994 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9994 246 4
  · have he : independentCachedBranchMembers9994.erase 246=independentCachedBranchMembers9992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9992
  · have he : independentCachedBranchMembers9994.filter (independentCachedEdge 246)=independentCachedBranchMembers9993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9993
def independentCachedBranchMembers9995 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9995 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9995 136 5
  · have he : independentCachedBranchMembers9995.erase 136=independentCachedBranchMembers9987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9987
  · have he : independentCachedBranchMembers9995.filter (independentCachedEdge 136)=independentCachedBranchMembers9994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9994
def independentCachedBranchMembers9996 : Finset ℕ := ([18,72,136,238,1590,1644,1686,1706,1708,1738,1740,1776,2614,2646,2666,2668,2710,2732,2762,2764,2800,3118,3150,3186,3188,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9996 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9996 5 (fun x => (if x<2668 then (if x<1706 then (if x<238 then (if x<72 then 0 else (if x<136 then 0 else 1)) else (if x<1644 then (if x<1590 then 1 else 0) else (if x<1686 then 0 else 2))) else (if x<1776 then (if x<1738 then (if x<1708 then 1 else 2) else (if x<1740 then 2 else 1)) else (if x<2646 then (if x<2614 then 2 else 3) else (if x<2666 then 4 else 3)))) else (if x<3150 then (if x<2762 then (if x<2710 then 4 else (if x<2732 then 0 else 1)) else (if x<2800 then (if x<2764 then 1 else 0) else (if x<3118 then 3 else 3))) else (if x<3250 then (if x<3188 then (if x<3186 then 4 else 3) else (if x<3214 then 4 else 1)) else (if x<3282 then (if x<3252 then 0 else 2) else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9997 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9997 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9997 3312 5
  · have he : independentCachedBranchMembers9997.erase 3312=independentCachedBranchMembers9995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9995
  · have he : independentCachedBranchMembers9997.filter (independentCachedEdge 3312)=independentCachedBranchMembers9996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9996
def independentCachedBranchMembers9998 : Finset ℕ := ([144,246,1590,1614,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9998 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9998 5 (fun x => (if x<2638 then (if x<1706 then (if x<1590 then (if x<246 then 0 else 0) else (if x<1614 then 1 else (if x<1686 then 1 else 0))) else (if x<1746 then (if x<1716 then 1 else (if x<1740 then 2 else 2)) else (if x<1776 then 1 else (if x<2614 then 0 else 2)))) else (if x<3158 then (if x<2710 then (if x<2668 then 2 else (if x<2674 then 3 else 3)) else (if x<2800 then 4 else (if x<3118 then 4 else 1))) else (if x<3214 then (if x<3178 then 1 else (if x<3188 then 3 else 3)) else (if x<3250 then 4 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9999 : Finset ℕ := ([246,1706,1746,1776,2674,2800,3118,3158,3188,3214] : List ℕ).toFinset
theorem independentCachedBranchBound9999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9999 4 (fun x => (if x<2800 then (if x<1746 then (if x<1706 then 0 else 1) else (if x<1776 then 0 else (if x<2674 then 1 else 0))) else (if x<3158 then (if x<3118 then 2 else 1) else (if x<3188 then 0 else (if x<3214 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10000 : Finset ℕ := ([72,144,246,1590,1614,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10000 72 4
  · have he : independentCachedBranchMembers10000.erase 72=independentCachedBranchMembers9998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9998
  · have he : independentCachedBranchMembers10000.filter (independentCachedEdge 72)=independentCachedBranchMembers9999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9999
def independentCachedBranchMembers10001 : Finset ℕ := ([144,1686,1706,1746,2668,2710,3118,3158,3178,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10001 4 (fun x => (if x<2710 then (if x<1706 then (if x<1686 then 0 else 0) else (if x<1746 then 1 else (if x<2668 then 1 else 0))) else (if x<3158 then (if x<3118 then 2 else 1) else (if x<3178 then 1 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10002 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10002 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10002 48 4
  · have he : independentCachedBranchMembers10002.erase 48=independentCachedBranchMembers10000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10000
  · have he : independentCachedBranchMembers10002.filter (independentCachedEdge 48)=independentCachedBranchMembers10001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10001
def independentCachedBranchMembers10003 : Finset ℕ := ([72,144,1590,1740,1746,1776,2638,2668,2674,2710,3118,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10003 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10003 4 (fun x => (if x<2638 then (if x<1740 then (if x<144 then 0 else (if x<1590 then 0 else 1)) else (if x<1746 then 2 else (if x<1776 then 1 else 2))) else (if x<2710 then (if x<2668 then 0 else (if x<2674 then 3 else 1)) else (if x<3118 then 0 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10004 : Finset ℕ := ([48,72,144,246,1590,1614,1650,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10004 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10004 1650 4
  · have he : independentCachedBranchMembers10004.erase 1650=independentCachedBranchMembers10002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10002
  · have he : independentCachedBranchMembers10004.filter (independentCachedEdge 1650)=independentCachedBranchMembers10003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10003
def independentCachedBranchMembers10005 : Finset ℕ := ([48,246,1614,1686,1740,1746,2614,2668,2674,2800,3158,3214] : List ℕ).toFinset
theorem independentCachedBranchBound10005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10005 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10005 4 (fun x => (if x<2614 then (if x<1686 then (if x<246 then 0 else (if x<1614 then 0 else 1)) else (if x<1740 then 1 else (if x<1746 then 2 else 2))) else (if x<2800 then (if x<2668 then 0 else (if x<2674 then 1 else 2)) else (if x<3158 then 0 else (if x<3214 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10006 : Finset ℕ := ([48,72,144,246,1590,1614,1644,1650,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10006 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10006 1644 4
  · have he : independentCachedBranchMembers10006.erase 1644=independentCachedBranchMembers10004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10004
  · have he : independentCachedBranchMembers10006.filter (independentCachedEdge 1644)=independentCachedBranchMembers10005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10005
def independentCachedBranchMembers10007 : Finset ℕ := ([48,144,1614,1706,1716,1776,2638,2800,3118,3178,3188,3214] : List ℕ).toFinset
theorem independentCachedBranchBound10007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10007 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10007 4 (fun x => (if x<2638 then (if x<1706 then (if x<144 then 0 else (if x<1614 then 1 else 0)) else (if x<1716 then 2 else (if x<1776 then 1 else 2))) else (if x<3178 then (if x<2800 then 1 else (if x<3118 then 0 else 2)) else (if x<3188 then 1 else (if x<3214 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10008 : Finset ℕ := ([18,48,72,144,246,1590,1614,1644,1650,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10008 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10008 18 4
  · have he : independentCachedBranchMembers10008.erase 18=independentCachedBranchMembers10006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10006
  · have he : independentCachedBranchMembers10008.filter (independentCachedEdge 18)=independentCachedBranchMembers10007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10007
def independentCachedBranchMembers10009 : Finset ℕ := ([72,246,1590,1686,1706,1716,2614,2710,3158,3178,3188,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10009 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10009 4 (fun x => (if x<2614 then (if x<1686 then (if x<246 then 0 else (if x<1590 then 1 else 0)) else (if x<1706 then 1 else (if x<1716 then 2 else 2))) else (if x<3178 then (if x<2710 then 1 else (if x<3158 then 0 else 1)) else (if x<3188 then 2 else (if x<3304 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10010 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10010 12 4
  · have he : independentCachedBranchMembers10010.erase 12=independentCachedBranchMembers10008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10008
  · have he : independentCachedBranchMembers10010.filter (independentCachedEdge 12)=independentCachedBranchMembers10009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10009
def independentCachedBranchMembers10011 : Finset ℕ := ([144,246,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,3118,3158,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10011 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10011 4 (fun x => (if x<2614 then (if x<1716 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3118 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3158 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10012 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1706,1716,1740,1746,1776,2614,2638,2668,2674,2710,2764,2800,3118,3158,3178,3188,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10012 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10012 2764 4
  · have he : independentCachedBranchMembers10012.erase 2764=independentCachedBranchMembers10010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10010
  · have he : independentCachedBranchMembers10012.filter (independentCachedEdge 2764)=independentCachedBranchMembers10011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10011
def independentCachedBranchMembers10013 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3242,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10013 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10013 3242 5
  · have he : independentCachedBranchMembers10013.erase 3242=independentCachedBranchMembers9997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9997
  · have he : independentCachedBranchMembers10013.filter (independentCachedEdge 3242)=independentCachedBranchMembers10012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10012
def independentCachedBranchMembers10014 : Finset ℕ := ([12,48,136,238,1614,1650,1686,1706,1708,1738,1740,1776,2606,2638,2674,2676,2710,2732,2762,2764,2800,3126,3158,3178,3180,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10014 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10014 5 (fun x => (if x<2676 then (if x<1706 then (if x<238 then (if x<48 then 0 else (if x<136 then 0 else 1)) else (if x<1650 then (if x<1614 then 1 else 0) else (if x<1686 then 0 else 2))) else (if x<1776 then (if x<1738 then (if x<1708 then 1 else 2) else (if x<1740 then 2 else 1)) else (if x<2638 then (if x<2606 then 2 else 3) else (if x<2674 then 4 else 3)))) else (if x<3158 then (if x<2762 then (if x<2710 then 4 else (if x<2732 then 3 else 1)) else (if x<2800 then (if x<2764 then 1 else 0) else (if x<3126 then 0 else 3))) else (if x<3250 then (if x<3180 then (if x<3178 then 4 else 3) else (if x<3214 then 4 else 0)) else (if x<3282 then (if x<3252 then 0 else 2) else (if x<3304 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10015 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10015 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10015 3222 5
  · have he : independentCachedBranchMembers10015.erase 3222=independentCachedBranchMembers10013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10013
  · have he : independentCachedBranchMembers10015.filter (independentCachedEdge 3222)=independentCachedBranchMembers10014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10014
end EntropyDesigns.QuadraticRefinement
