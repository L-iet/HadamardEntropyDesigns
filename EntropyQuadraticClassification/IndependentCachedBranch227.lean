/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch226
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10048 : Finset ℕ := ([72,238,1590,1614,1650,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,2738,2762,2764,2800,3118,3158,3178,3180,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10048 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10048 5 (fun x => (if x<2666 then (if x<1706 then (if x<1614 then (if x<238 then 0 else (if x<1590 then 0 else 1)) else (if x<1650 then 0 else (if x<1686 then 2 else 2))) else (if x<1748 then (if x<1708 then 1 else (if x<1746 then 3 else 1)) else (if x<2606 then (if x<1768 then 3 else 0) else (if x<2646 then 1 else 1)))) else (if x<3158 then (if x<2762 then (if x<2668 then 0 else (if x<2738 then 4 else 1)) else (if x<2800 then (if x<2764 then 1 else 0) else (if x<3118 then 4 else 3))) else (if x<3214 then (if x<3178 then 2 else (if x<3180 then 2 else 0)) else (if x<3252 then (if x<3250 then 2 else 2) else (if x<3276 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10049 : Finset ℕ := ([238,1590,1650,1706,1708,1768,2646,2762,2764,3158,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10049 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10049 4 (fun x => (if x<2646 then (if x<1706 then (if x<1590 then 0 else (if x<1650 then 1 else 2)) else (if x<1708 then 0 else (if x<1768 then 1 else 2))) else (if x<3158 then (if x<2762 then 1 else (if x<2764 then 0 else 1)) else (if x<3214 then 2 else (if x<3276 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10050 : Finset ℕ := ([72,144,238,1590,1614,1650,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,2738,2762,2764,2800,3118,3158,3178,3180,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10050 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10050 144 4
  · have he : independentCachedBranchMembers10050.erase 144=independentCachedBranchMembers10048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10048
  · have he : independentCachedBranchMembers10050.filter (independentCachedEdge 144)=independentCachedBranchMembers10049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10049
def independentCachedBranchMembers10051 : Finset ℕ := ([72,1590,1686,1706,1748,1768,2646,2666,2762,3158,3178,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10051 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10051 4 (fun x => (if x<2646 then (if x<1706 then (if x<1590 then 0 else (if x<1686 then 0 else 1)) else (if x<1748 then 1 else (if x<1768 then 2 else 2))) else (if x<3158 then (if x<2666 then 1 else (if x<2762 then 1 else 0)) else (if x<3178 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10052 : Finset ℕ := ([12,72,144,238,1590,1614,1650,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,2738,2762,2764,2800,3118,3158,3178,3180,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10052 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10052 12 4
  · have he : independentCachedBranchMembers10052.erase 12=independentCachedBranchMembers10050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10050
  · have he : independentCachedBranchMembers10052.filter (independentCachedEdge 12)=independentCachedBranchMembers10051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10051
def independentCachedBranchMembers10053 : Finset ℕ := ([238,1590,1686,1706,1708,2646,2666,2668,2762,2764,2800,3118,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10053 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10053 4 (fun x => (if x<2668 then (if x<1706 then (if x<1590 then 0 else (if x<1686 then 1 else 2)) else (if x<2646 then (if x<1708 then 0 else 1) else (if x<2666 then 1 else 0))) else (if x<3118 then (if x<2764 then (if x<2762 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3250 then (if x<3214 then 0 else 3) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10054 : Finset ℕ := ([1706,1708,2646,2800,3118,3214] : List ℕ).toFinset
theorem independentCachedBranchBound10054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10054 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10054 3 (fun x => (if x<2800 then (if x<1708 then 0 else (if x<2646 then 1 else 0)) else (if x<3118 then 2 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10055 : Finset ℕ := ([72,238,1590,1686,1706,1708,2646,2666,2668,2762,2764,2800,3118,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10055 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10055 72 3
  · have he : independentCachedBranchMembers10055.erase 72=independentCachedBranchMembers10053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10053
  · have he : independentCachedBranchMembers10055.filter (independentCachedEdge 72)=independentCachedBranchMembers10054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10054
def independentCachedBranchMembers10056 : Finset ℕ := ([12,72,144,238,1590,1614,1650,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,2738,2762,2764,2800,3118,3158,3178,3180,3214,3250,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10056 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10056 3312 4
  · have he : independentCachedBranchMembers10056.erase 3312=independentCachedBranchMembers10052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10052
  · have he : independentCachedBranchMembers10056.filter (independentCachedEdge 3312)=independentCachedBranchMembers10055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10055
def independentCachedBranchMembers10057 : Finset ℕ := ([72,144,1590,1746,1748,1768,2606,2762,2764,2800,3158,3178,3180,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10057 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10057 4 (fun x => (if x<2764 then (if x<1748 then (if x<1590 then (if x<144 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2606 then (if x<1768 then 2 else 2) else (if x<2762 then 1 else 1))) else (if x<3180 then (if x<3158 then (if x<2800 then 2 else 2) else (if x<3178 then 3 else 0)) else (if x<3250 then (if x<3214 then 3 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10058 : Finset ℕ := ([12,72,144,238,1590,1614,1650,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,2702,2738,2762,2764,2800,3118,3158,3178,3180,3214,3250,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10058 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10058 2702 4
  · have he : independentCachedBranchMembers10058.erase 2702=independentCachedBranchMembers10056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10056
  · have he : independentCachedBranchMembers10058.filter (independentCachedEdge 2702)=independentCachedBranchMembers10057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10057
def independentCachedBranchMembers10059 : Finset ℕ := ([238,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,3118,3158,3178,3180] : List ℕ).toFinset
theorem independentCachedBranchBound10059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10059 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10059 4 (fun x => (if x<2606 then (if x<1708 then (if x<1686 then 0 else (if x<1706 then 1 else 0)) else (if x<1748 then (if x<1746 then 1 else 2) else (if x<1768 then 3 else 2))) else (if x<3118 then (if x<2666 then (if x<2646 then 0 else 1) else (if x<2668 then 3 else 1)) else (if x<3178 then (if x<3158 then 3 else 2) else (if x<3180 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10060 : Finset ℕ := ([238,1706,1708,1768,2646,3158] : List ℕ).toFinset
theorem independentCachedBranchBound10060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10060 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10060 3 (fun x => (if x<1768 then (if x<1706 then 0 else (if x<1708 then 0 else 1)) else (if x<2646 then 2 else (if x<3158 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10061 : Finset ℕ := ([144,238,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,3118,3158,3178,3180] : List ℕ).toFinset
theorem independentCachedBranchBound10061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10061 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10061 144 3
  · have he : independentCachedBranchMembers10061.erase 144=independentCachedBranchMembers10059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10059
  · have he : independentCachedBranchMembers10061.filter (independentCachedEdge 144)=independentCachedBranchMembers10060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10060
def independentCachedBranchMembers10062 : Finset ℕ := ([12,48,72,144,238,1590,1614,1650,1686,1706,1708,1746,1748,1768,2606,2646,2666,2668,2702,2738,2762,2764,2800,3118,3158,3178,3180,3214,3250,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10062 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10062 48 4
  · have he : independentCachedBranchMembers10062.erase 48=independentCachedBranchMembers10058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10058
  · have he : independentCachedBranchMembers10062.filter (independentCachedEdge 48)=independentCachedBranchMembers10061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10061
def independentCachedBranchMembers10063 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10063 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10063 1622 5
  · have he : independentCachedBranchMembers10063.erase 1622=independentCachedBranchMembers10047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10047
  · have he : independentCachedBranchMembers10063.filter (independentCachedEdge 1622)=independentCachedBranchMembers10062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10062
def independentCachedBranchMembers10064 : Finset ℕ := ([18,48,136,246,1590,1614,1644,1678,1706,1708,1746,1748,1776,2606,2646,2674,2676,2710,2738,2762,2764,3118,3158,3186,3188,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10064 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10064 5 (fun x => (if x<2646 then (if x<1678 then (if x<246 then (if x<48 then 0 else (if x<136 then 1 else 0)) else (if x<1614 then (if x<1590 then 1 else 0) else (if x<1644 then 2 else 3))) else (if x<1746 then (if x<1706 then 3 else (if x<1708 then 2 else 0)) else (if x<1776 then (if x<1748 then 2 else 3) else (if x<2606 then 1 else 2)))) else (if x<3118 then (if x<2710 then (if x<2674 then 0 else (if x<2676 then 1 else 3)) else (if x<2762 then (if x<2738 then 3 else 2) else (if x<2764 then 2 else 0))) else (if x<3250 then (if x<3186 then (if x<3158 then 4 else 4) else (if x<3188 then 0 else 1)) else (if x<3276 then (if x<3252 then 1 else 4) else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10065 : Finset ℕ := ([136,1614,1706,1708,1776,2606,2674,2676,2710,2762,2764,3158,3250,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10065 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10065 4 (fun x => (if x<2676 then (if x<1708 then (if x<1614 then 0 else (if x<1706 then 1 else 0)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2674 then 1 else 2))) else (if x<3158 then (if x<2762 then (if x<2710 then 0 else 3) else (if x<2764 then 3 else 1)) else (if x<3252 then (if x<3250 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10066 : Finset ℕ := ([1706,1708,2606,2710,3158,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10066 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10066 3 (fun x => (if x<2710 then (if x<1708 then 0 else (if x<2606 then 1 else 0)) else (if x<3158 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10067 : Finset ℕ := ([48,136,1614,1706,1708,1776,2606,2674,2676,2710,2762,2764,3158,3250,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10067 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10067 48 3
  · have he : independentCachedBranchMembers10067.erase 48=independentCachedBranchMembers10065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10065
  · have he : independentCachedBranchMembers10067.filter (independentCachedEdge 48)=independentCachedBranchMembers10066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10066
def independentCachedBranchMembers10068 : Finset ℕ := ([18,48,136,246,1590,1614,1644,1678,1706,1708,1746,1748,1776,2606,2646,2674,2676,2710,2738,2762,2764,3118,3158,3186,3188,3222,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10068 3222 4
  · have he : independentCachedBranchMembers10068.erase 3222=independentCachedBranchMembers10064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10064
  · have he : independentCachedBranchMembers10068.filter (independentCachedEdge 3222)=independentCachedBranchMembers10067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10067
def independentCachedBranchMembers10069 : Finset ℕ := ([48,246,1614,1678,1746,1748,2646,2710,2762,2764,3118,3186,3188,3250,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10069 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10069 4 (fun x => (if x<2762 then (if x<1746 then (if x<1614 then (if x<246 then 0 else 0) else (if x<1678 then 1 else 2)) else (if x<2646 then (if x<1748 then 1 else 2) else (if x<2710 then 1 else 2))) else (if x<3188 then (if x<3118 then (if x<2764 then 1 else 2) else (if x<3186 then 3 else 0)) else (if x<3252 then (if x<3250 then 3 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10070 : Finset ℕ := ([18,48,136,246,1590,1614,1644,1678,1706,1708,1746,1748,1776,2606,2646,2674,2676,2710,2738,2762,2764,2792,3118,3158,3186,3188,3222,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10070 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10070 2792 4
  · have he : independentCachedBranchMembers10070.erase 2792=independentCachedBranchMembers10068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10068
  · have he : independentCachedBranchMembers10070.filter (independentCachedEdge 2792)=independentCachedBranchMembers10069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10069
def independentCachedBranchMembers10071 : Finset ℕ := ([136,246,1678,1706,1708,1746,1748,1776,2606,2646,2674,2676,3118,3158,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10071 4 (fun x => (if x<2606 then (if x<1708 then (if x<1678 then (if x<246 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<1748 then (if x<1746 then 3 else 1) else (if x<1776 then 3 else 2))) else (if x<3118 then (if x<2674 then (if x<2646 then 2 else 1) else (if x<2676 then 0 else 2)) else (if x<3186 then (if x<3158 then 3 else 3) else (if x<3188 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10072 : Finset ℕ := ([18,48,72,136,246,1590,1614,1644,1678,1706,1708,1746,1748,1776,2606,2646,2674,2676,2710,2738,2762,2764,2792,3118,3158,3186,3188,3222,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10072 72 4
  · have he : independentCachedBranchMembers10072.erase 72=independentCachedBranchMembers10070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10070
  · have he : independentCachedBranchMembers10072.filter (independentCachedEdge 72)=independentCachedBranchMembers10071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10071
def independentCachedBranchMembers10073 : Finset ℕ := ([12,18,48,72,136,144,238,246,1582,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10073 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10073 1582 5
  · have he : independentCachedBranchMembers10073.erase 1582=independentCachedBranchMembers10063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10063
  · have he : independentCachedBranchMembers10073.filter (independentCachedEdge 1582)=independentCachedBranchMembers10072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10072
def independentCachedBranchMembers10074 : Finset ℕ := ([48,72,144,238,1614,1644,1686,1714,1716,1738,1740,1768,2614,2638,2666,2668,2710,2738,2762,2764,3126,3150,3178,3180,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10074 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10074 5 (fun x => (if x<2666 then (if x<1714 then (if x<238 then (if x<72 then 0 else (if x<144 then 0 else 1)) else (if x<1644 then (if x<1614 then 2 else 0) else (if x<1686 then 1 else 3))) else (if x<1740 then (if x<1716 then 4 else (if x<1738 then 1 else 2)) else (if x<2614 then (if x<1768 then 3 else 4) else (if x<2638 then 3 else 1)))) else (if x<3150 then (if x<2738 then (if x<2668 then 2 else (if x<2710 then 3 else 1)) else (if x<2764 then (if x<2762 then 0 else 0) else (if x<3126 then 2 else 4))) else (if x<3250 then (if x<3178 then 2 else (if x<3180 then 1 else 4)) else (if x<3276 then (if x<3252 then 1 else 0) else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10075 : Finset ℕ := ([48,144,238,1614,1716,1738,2638,2666,2762,3150,3178,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10075 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10075 4 (fun x => (if x<2638 then (if x<1614 then (if x<144 then 0 else (if x<238 then 1 else 2)) else (if x<1716 then 0 else (if x<1738 then 1 else 2))) else (if x<3150 then (if x<2666 then 1 else (if x<2762 then 2 else 0)) else (if x<3178 then 2 else (if x<3252 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10076 : Finset ℕ := ([18,48,72,144,238,1614,1644,1686,1714,1716,1738,1740,1768,2614,2638,2666,2668,2710,2738,2762,2764,3126,3150,3178,3180,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10076 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10076 18 4
  · have he : independentCachedBranchMembers10076.erase 18=independentCachedBranchMembers10074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10074
  · have he : independentCachedBranchMembers10076.filter (independentCachedEdge 18)=independentCachedBranchMembers10075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10075
def independentCachedBranchMembers10077 : Finset ℕ := ([48,238,1614,1686,1738,1740,2638,2710,2762,2764,3126,3178,3180,3250,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10077 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10077 4 (fun x => (if x<2762 then (if x<1738 then (if x<1614 then (if x<238 then 0 else 1) else (if x<1686 then 0 else 2)) else (if x<2638 then (if x<1740 then 1 else 2) else (if x<2710 then 1 else 3))) else (if x<3180 then (if x<3126 then (if x<2764 then 0 else 3) else (if x<3178 then 2 else 1)) else (if x<3252 then (if x<3250 then 2 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10078 : Finset ℕ := ([18,48,72,144,238,1614,1644,1686,1714,1716,1738,1740,1768,2614,2638,2666,2668,2710,2738,2762,2764,3126,3150,3178,3180,3222,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10078 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10078 3222 4
  · have he : independentCachedBranchMembers10078.erase 3222=independentCachedBranchMembers10076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10076
  · have he : independentCachedBranchMembers10078.filter (independentCachedEdge 3222)=independentCachedBranchMembers10077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10077
def independentCachedBranchMembers10079 : Finset ℕ := ([48,144,1614,1714,1716,1768,2614,2666,2668,2710,2762,2764,3150,3250,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10079 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10079 4 (fun x => (if x<2668 then (if x<1716 then (if x<1614 then (if x<144 then 0 else 1) else (if x<1714 then 0 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2666 then 2 else 2))) else (if x<3150 then (if x<2762 then (if x<2710 then 1 else 3) else (if x<2764 then 0 else 3)) else (if x<3252 then (if x<3250 then 1 else 3) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
