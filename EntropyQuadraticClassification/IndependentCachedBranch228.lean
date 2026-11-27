/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch227
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10080 : Finset ℕ := ([18,48,72,144,238,1614,1644,1686,1714,1716,1738,1740,1768,2614,2638,2666,2668,2710,2738,2762,2764,2792,3126,3150,3178,3180,3222,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10080 2792 4
  · have he : independentCachedBranchMembers10080.erase 2792=independentCachedBranchMembers10078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10078
  · have he : independentCachedBranchMembers10080.filter (independentCachedEdge 2792)=independentCachedBranchMembers10079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10079
def independentCachedBranchMembers10081 : Finset ℕ := ([144,238,1686,1714,1716,1738,1740,1768,2614,2638,2666,2668,3126,3150,3178,3180] : List ℕ).toFinset
theorem independentCachedBranchBound10081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10081 4 (fun x => (if x<2614 then (if x<1716 then (if x<1686 then (if x<238 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<1740 then (if x<1738 then 3 else 1) else (if x<1768 then 3 else 2))) else (if x<3126 then (if x<2666 then (if x<2638 then 2 else 1) else (if x<2668 then 0 else 2)) else (if x<3178 then (if x<3150 then 3 else 3) else (if x<3180 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10082 : Finset ℕ := ([18,48,72,144,238,1590,1614,1644,1686,1714,1716,1738,1740,1768,2614,2638,2666,2668,2710,2738,2762,2764,2792,3126,3150,3178,3180,3222,3250,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10082 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10082 1590 4
  · have he : independentCachedBranchMembers10082.erase 1590=independentCachedBranchMembers10080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10080
  · have he : independentCachedBranchMembers10082.filter (independentCachedEdge 1590)=independentCachedBranchMembers10081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10081
def independentCachedBranchMembers10083 : Finset ℕ := ([12,18,48,72,80,136,144,238,246,1582,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10083 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10083 80 5
  · have he : independentCachedBranchMembers10083.erase 80=independentCachedBranchMembers10073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10073
  · have he : independentCachedBranchMembers10083.filter (independentCachedEdge 80)=independentCachedBranchMembers10082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10082
def independentCachedBranchMembers10084 : Finset ℕ := ([48,136,246,1590,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10084 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10084 5 (fun x => (if x<2674 then (if x<1716 then (if x<1590 then (if x<136 then 0 else (if x<246 then 0 else 1)) else (if x<1678 then 0 else (if x<1714 then 0 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1740 then 3 else 2)) else (if x<2614 then 3 else (if x<2638 then 1 else 2)))) else (if x<3150 then (if x<2764 then (if x<2676 then 0 else (if x<2762 then 3 else 0)) else (if x<2800 then 4 else (if x<3126 then 1 else 4))) else (if x<3214 then (if x<3186 then 4 else (if x<3188 then 1 else 0)) else (if x<3250 then 3 else (if x<3252 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10085 : Finset ℕ := ([136,246,1678,1776,2674,2676,2800,3186,3188,3214] : List ℕ).toFinset
theorem independentCachedBranchBound10085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10085 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10085 4 (fun x => (if x<2676 then (if x<1678 then (if x<246 then 0 else 1) else (if x<1776 then 0 else (if x<2674 then 1 else 0))) else (if x<3186 then (if x<2800 then 1 else 2) else (if x<3188 then 1 else (if x<3214 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10086 : Finset ℕ := ([48,72,136,246,1590,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10086 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10086 72 4
  · have he : independentCachedBranchMembers10086.erase 72=independentCachedBranchMembers10084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10084
  · have he : independentCachedBranchMembers10086.filter (independentCachedEdge 72)=independentCachedBranchMembers10085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10085
def independentCachedBranchMembers10087 : Finset ℕ := ([246,1716,1740,1776,2676,2764,2800,3126,3150,3186,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10087 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10087 4 (fun x => (if x<2800 then (if x<1776 then (if x<1716 then 0 else (if x<1740 then 0 else 1)) else (if x<2676 then 1 else (if x<2764 then 0 else 2))) else (if x<3186 then (if x<3126 then 2 else (if x<3150 then 0 else 1)) else (if x<3214 then 1 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10088 : Finset ℕ := ([48,72,136,246,1590,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10088 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10088 3276 4
  · have he : independentCachedBranchMembers10088.erase 3276=independentCachedBranchMembers10086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10086
  · have he : independentCachedBranchMembers10088.filter (independentCachedEdge 3276)=independentCachedBranchMembers10087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10087
def independentCachedBranchMembers10089 : Finset ℕ := ([136,1678,1714,1738,2614,2638,2674,2764,2800,3188,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10089 4 (fun x => (if x<2674 then (if x<1738 then (if x<1678 then 0 else (if x<1714 then 0 else 1)) else (if x<2614 then 1 else (if x<2638 then 1 else 1))) else (if x<3188 then (if x<2764 then 0 else (if x<2800 then 2 else 2)) else (if x<3214 then 0 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10090 : Finset ℕ := ([48,72,136,246,1590,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2738,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10090 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10090 2738 4
  · have he : independentCachedBranchMembers10090.erase 2738=independentCachedBranchMembers10088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10088
  · have he : independentCachedBranchMembers10090.filter (independentCachedEdge 2738)=independentCachedBranchMembers10089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10089
def independentCachedBranchMembers10091 : Finset ℕ := ([72,1590,1678,1714,1740,1776,2638,2674,2762,3150,3186,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10091 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10091 4 (fun x => (if x<2638 then (if x<1714 then (if x<1590 then 0 else (if x<1678 then 0 else 1)) else (if x<1740 then 1 else (if x<1776 then 2 else 2))) else (if x<3150 then (if x<2674 then 1 else (if x<2762 then 1 else 0)) else (if x<3186 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10092 : Finset ℕ := ([48,72,136,246,1590,1650,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2738,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10092 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10092 1650 4
  · have he : independentCachedBranchMembers10092.erase 1650=independentCachedBranchMembers10090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10090
  · have he : independentCachedBranchMembers10092.filter (independentCachedEdge 1650)=independentCachedBranchMembers10091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10091
def independentCachedBranchMembers10093 : Finset ℕ := ([72,136,246,1590,1716,1738,2614,2676,2762,3126,3188,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10093 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10093 4 (fun x => (if x<2614 then (if x<1590 then (if x<136 then 0 else (if x<246 then 1 else 2)) else (if x<1716 then 0 else (if x<1738 then 2 else 1))) else (if x<3126 then (if x<2676 then 1 else (if x<2762 then 2 else 0)) else (if x<3188 then 2 else (if x<3252 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10094 : Finset ℕ := ([12,48,72,136,246,1590,1650,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2738,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound10094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10094 12 4
  · have he : independentCachedBranchMembers10094.erase 12=independentCachedBranchMembers10092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10092
  · have he : independentCachedBranchMembers10094.filter (independentCachedEdge 12)=independentCachedBranchMembers10093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10093
def independentCachedBranchMembers10095 : Finset ℕ := ([72,136,1590,1738,1740,1776,2614,2762,2764,2800,3150,3186,3188,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10095 4 (fun x => (if x<2764 then (if x<1740 then (if x<1590 then (if x<136 then 0 else 1) else (if x<1738 then 0 else 1)) else (if x<2614 then (if x<1776 then 2 else 2) else (if x<2762 then 1 else 0))) else (if x<3188 then (if x<3150 then (if x<2800 then 3 else 3) else (if x<3186 then 2 else 2)) else (if x<3250 then (if x<3214 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10096 : Finset ℕ := ([12,48,72,136,246,1590,1650,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2738,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10096 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10096 3312 4
  · have he : independentCachedBranchMembers10096.erase 3312=independentCachedBranchMembers10094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10094
  · have he : independentCachedBranchMembers10096.filter (independentCachedEdge 3312)=independentCachedBranchMembers10095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10095
def independentCachedBranchMembers10097 : Finset ℕ := ([72,246,1590,1678,1714,1716,2638,2674,2676,2762,2764,2800,3126,3214,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10097 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10097 4 (fun x => (if x<2676 then (if x<1714 then (if x<1590 then (if x<246 then 0 else 1) else (if x<1678 then 0 else 2)) else (if x<2638 then (if x<1716 then 1 else 2) else (if x<2674 then 2 else 1))) else (if x<3126 then (if x<2764 then (if x<2762 then 2 else 0) else (if x<2800 then 3 else 3)) else (if x<3250 then (if x<3214 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10098 : Finset ℕ := ([12,48,72,136,246,1590,1650,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2702,2738,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10098 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10098 2702 4
  · have he : independentCachedBranchMembers10098.erase 2702=independentCachedBranchMembers10096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10096
  · have he : independentCachedBranchMembers10098.filter (independentCachedEdge 2702)=independentCachedBranchMembers10097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10097
def independentCachedBranchMembers10099 : Finset ℕ := ([246,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,3126,3150,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10099 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10099 4 (fun x => (if x<2614 then (if x<1716 then (if x<1678 then 0 else (if x<1714 then 1 else 0)) else (if x<1740 then (if x<1738 then 1 else 2) else (if x<1776 then 3 else 2))) else (if x<3126 then (if x<2674 then (if x<2638 then 0 else 1) else (if x<2676 then 3 else 1)) else (if x<3186 then (if x<3150 then 3 else 2) else (if x<3188 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10100 : Finset ℕ := ([246,1714,1716,1776,2638,3150] : List ℕ).toFinset
theorem independentCachedBranchBound10100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10100 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10100 3 (fun x => (if x<1776 then (if x<1714 then 0 else (if x<1716 then 0 else 1)) else (if x<2638 then 2 else (if x<3150 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10101 : Finset ℕ := ([136,246,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,3126,3150,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10101 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10101 136 3
  · have he : independentCachedBranchMembers10101.erase 136=independentCachedBranchMembers10099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10099
  · have he : independentCachedBranchMembers10101.filter (independentCachedEdge 136)=independentCachedBranchMembers10100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10100
def independentCachedBranchMembers10102 : Finset ℕ := ([12,48,72,136,246,1590,1614,1650,1678,1714,1716,1738,1740,1776,2614,2638,2674,2676,2702,2738,2762,2764,2800,3126,3150,3186,3188,3214,3250,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10102 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10102 1614 4
  · have he : independentCachedBranchMembers10102.erase 1614=independentCachedBranchMembers10098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10098
  · have he : independentCachedBranchMembers10102.filter (independentCachedEdge 1614)=independentCachedBranchMembers10101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10101
def independentCachedBranchMembers10103 : Finset ℕ := ([12,18,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10103 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10103 40 5
  · have he : independentCachedBranchMembers10103.erase 40=independentCachedBranchMembers10083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10083
  · have he : independentCachedBranchMembers10103.filter (independentCachedEdge 40)=independentCachedBranchMembers10102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10102
def independentCachedBranchMembers10104 : Finset ℕ := ([72,136,238,1590,1614,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10104 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10104 5 (fun x => (if x<2674 then (if x<1714 then (if x<1590 then (if x<136 then 0 else (if x<238 then 1 else 0)) else (if x<1678 then (if x<1614 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1768 then (if x<1738 then 2 else (if x<1748 then 2 else 2)) else (if x<2638 then (if x<2614 then 0 else 3) else (if x<2668 then 3 else 0)))) else (if x<3178 then (if x<2772 then (if x<2702 then 1 else (if x<2762 then 4 else 0)) else (if x<3118 then (if x<2792 then 3 else 4) else (if x<3158 then 3 else 3))) else (if x<3242 then (if x<3188 then 0 else (if x<3222 then 1 else 4)) else (if x<3276 then (if x<3252 then 2 else 2) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10105 : Finset ℕ := ([238,1708,1748,1768,2668,2772,2792,3118,3158,3178,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound10105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10105 4 (fun x => (if x<2792 then (if x<1768 then (if x<1708 then 0 else (if x<1748 then 0 else 1)) else (if x<2668 then 1 else (if x<2772 then 0 else 2))) else (if x<3178 then (if x<3118 then 2 else (if x<3158 then 0 else 1)) else (if x<3222 then 1 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10106 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10106 48 4
  · have he : independentCachedBranchMembers10106.erase 48=independentCachedBranchMembers10104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10104
  · have he : independentCachedBranchMembers10106.filter (independentCachedEdge 48)=independentCachedBranchMembers10105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10105
def independentCachedBranchMembers10107 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1768,2614,2638,2702,2792,3118,3158,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10107 4 (fun x => (if x<2614 then (if x<1590 then (if x<136 then (if x<72 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1678 then (if x<1614 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2638 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3158 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10108 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10108 3282 4
  · have he : independentCachedBranchMembers10108.erase 3282=independentCachedBranchMembers10106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10106
  · have he : independentCachedBranchMembers10108.filter (independentCachedEdge 3282)=independentCachedBranchMembers10107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10107
def independentCachedBranchMembers10109 : Finset ℕ := ([136,238,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,3118,3158,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10109 4 (fun x => (if x<2614 then (if x<1714 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3118 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3158 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10110 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1708,1714,1738,1748,1768,2614,2638,2668,2674,2702,2738,2762,2772,2792,3118,3158,3178,3188,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10110 2738 4
  · have he : independentCachedBranchMembers10110.erase 2738=independentCachedBranchMembers10108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10108
  · have he : independentCachedBranchMembers10110.filter (independentCachedEdge 2738)=independentCachedBranchMembers10109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10109
def independentCachedBranchMembers10111 : Finset ℕ := ([48,72,1590,1614,1708,1714,1738,1748,2668,2674,2702,2792,3178,3188,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10111 4 (fun x => (if x<2668 then (if x<1708 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3178 then (if x<2702 then (if x<2674 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3188 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
