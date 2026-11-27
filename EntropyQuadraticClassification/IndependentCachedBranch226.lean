/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch225
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10016 : Finset ℕ := ([12,48,144,246,1614,1650,1678,1714,1716,1746,1748,1768,2614,2646,2666,2668,2710,2732,2762,2764,2800,3118,3150,3186,3188,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10016 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10016 5 (fun x => (if x<2668 then (if x<1714 then (if x<246 then (if x<48 then 0 else (if x<144 then 0 else 1)) else (if x<1650 then (if x<1614 then 1 else 0) else (if x<1678 then 0 else 2))) else (if x<1768 then (if x<1746 then (if x<1716 then 1 else 2) else (if x<1748 then 2 else 1)) else (if x<2646 then (if x<2614 then 2 else 3) else (if x<2666 then 4 else 3)))) else (if x<3150 then (if x<2762 then (if x<2710 then 4 else (if x<2732 then 1 else 2)) else (if x<2800 then (if x<2764 then 2 else 0) else (if x<3118 then 0 else 3))) else (if x<3250 then (if x<3188 then (if x<3186 then 4 else 3) else (if x<3214 then 4 else 0)) else (if x<3282 then (if x<3252 then 0 else 1) else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10017 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10017 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10017 2792 5
  · have he : independentCachedBranchMembers10017.erase 2792=independentCachedBranchMembers10015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10015
  · have he : independentCachedBranchMembers10017.filter (independentCachedEdge 2792)=independentCachedBranchMembers10016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10016
def independentCachedBranchMembers10018 : Finset ℕ := ([18,48,72,136,238,1590,1614,1644,1650,1678,1708,1714,1738,1748,1768,2606,2646,2666,2676,2710,2764,2800,3126,3150,3180,3186,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10018 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10018 5 (fun x => (if x<1768 then (if x<1644 then (if x<136 then (if x<48 then 0 else (if x<72 then 1 else 0)) else (if x<1590 then (if x<238 then 1 else 2) else (if x<1614 then 0 else 2))) else (if x<1708 then (if x<1650 then 0 else (if x<1678 then 1 else 3)) else (if x<1738 then (if x<1714 then 2 else 3) else (if x<1748 then 1 else 3)))) else (if x<2800 then (if x<2666 then (if x<2606 then 3 else (if x<2646 then 2 else 4)) else (if x<2710 then (if x<2676 then 4 else 1) else (if x<2764 then 0 else 0))) else (if x<3180 then (if x<3126 then 3 else (if x<3150 then 1 else 4)) else (if x<3214 then (if x<3186 then 2 else 4) else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10019 : Finset ℕ := ([72,136,1590,1738,1748,1768,2646,2666,2676,2710,3126,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10019 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10019 4 (fun x => (if x<2646 then (if x<1738 then (if x<136 then 0 else (if x<1590 then 1 else 0)) else (if x<1748 then 1 else (if x<1768 then 2 else 2))) else (if x<2710 then (if x<2666 then 2 else (if x<2676 then 2 else 1)) else (if x<3126 then 0 else (if x<3304 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10020 : Finset ℕ := ([12,18,48,72,136,238,1590,1614,1644,1650,1678,1708,1714,1738,1748,1768,2606,2646,2666,2676,2710,2764,2800,3126,3150,3180,3186,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10020 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10020 12 4
  · have he : independentCachedBranchMembers10020.erase 12=independentCachedBranchMembers10018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10018
  · have he : independentCachedBranchMembers10020.filter (independentCachedEdge 12)=independentCachedBranchMembers10019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10019
def independentCachedBranchMembers10021 : Finset ℕ := ([136,238,1678,1708,1714,1738,1748,1768,2606,2646,2666,2676,3126,3150,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10021 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10021 4 (fun x => (if x<2606 then (if x<1714 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2666 then (if x<2646 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10022 : Finset ℕ := ([12,18,48,72,136,238,1590,1614,1644,1650,1678,1708,1714,1738,1748,1768,2606,2646,2666,2676,2710,2764,2800,3126,3150,3180,3186,3214,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10022 3250 4
  · have he : independentCachedBranchMembers10022.erase 3250=independentCachedBranchMembers10020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10020
  · have he : independentCachedBranchMembers10022.filter (independentCachedEdge 3250)=independentCachedBranchMembers10021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10021
def independentCachedBranchMembers10023 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2710,2732,2738,2762,2764,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10023 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10023 2772 5
  · have he : independentCachedBranchMembers10023.erase 2772=independentCachedBranchMembers10017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10017
  · have he : independentCachedBranchMembers10023.filter (independentCachedEdge 2772)=independentCachedBranchMembers10022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10022
def independentCachedBranchMembers10024 : Finset ℕ := ([18,72,144,246,1590,1644,1678,1714,1716,1746,1748,1768,2606,2638,2674,2676,2710,2732,2762,2764,2800,3126,3158,3178,3180,3214,3250,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10024 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10024 5 (fun x => (if x<2676 then (if x<1714 then (if x<246 then (if x<72 then 0 else (if x<144 then 0 else 1)) else (if x<1644 then (if x<1590 then 1 else 0) else (if x<1678 then 0 else 2))) else (if x<1768 then (if x<1746 then (if x<1716 then 1 else 2) else (if x<1748 then 2 else 1)) else (if x<2638 then (if x<2606 then 2 else 3) else (if x<2674 then 4 else 3)))) else (if x<3158 then (if x<2762 then (if x<2710 then 4 else (if x<2732 then 0 else 2)) else (if x<2800 then (if x<2764 then 2 else 0) else (if x<3126 then 1 else 3))) else (if x<3250 then (if x<3180 then (if x<3178 then 4 else 3) else (if x<3214 then 4 else 3)) else (if x<3282 then (if x<3252 then 0 else 1) else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10025 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10025 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10025 2702 5
  · have he : independentCachedBranchMembers10025.erase 2702=independentCachedBranchMembers10023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10023
  · have he : independentCachedBranchMembers10025.filter (independentCachedEdge 2702)=independentCachedBranchMembers10024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10024
def independentCachedBranchMembers10026 : Finset ℕ := ([144,246,1590,1614,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2800,3118,3158,3180,3186,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10026 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10026 5 (fun x => (if x<2676 then (if x<1714 then (if x<1614 then (if x<246 then 0 else (if x<1590 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 0 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1748 then 2 else 1)) else (if x<2638 then (if x<2614 then 0 else 2) else (if x<2666 then 2 else 3)))) else (if x<3180 then (if x<2738 then (if x<2710 then 3 else (if x<2732 then 4 else 3)) else (if x<3118 then (if x<2800 then 0 else 4) else (if x<3158 then 1 else 1))) else (if x<3252 then (if x<3186 then 3 else (if x<3214 then 3 else 4)) else (if x<3282 then (if x<3276 then 0 else 1) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10027 : Finset ℕ := ([246,1708,1748,1776,2676,2732,2800,3118,3158,3186,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound10027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10027 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10027 4 (fun x => (if x<2800 then (if x<1776 then (if x<1708 then 0 else (if x<1748 then 1 else 0)) else (if x<2676 then 1 else (if x<2732 then 0 else 2))) else (if x<3186 then (if x<3118 then 2 else (if x<3158 then 1 else 0)) else (if x<3214 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10028 : Finset ℕ := ([72,144,246,1590,1614,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2800,3118,3158,3180,3186,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10028 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10028 72 4
  · have he : independentCachedBranchMembers10028.erase 72=independentCachedBranchMembers10026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10026
  · have he : independentCachedBranchMembers10028.filter (independentCachedEdge 72)=independentCachedBranchMembers10027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10027
def independentCachedBranchMembers10029 : Finset ℕ := ([144,1686,1708,1748,2666,2710,2732,3118,3158,3180,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10029 4 (fun x => (if x<2732 then (if x<1748 then (if x<1686 then 0 else (if x<1708 then 0 else 1)) else (if x<2666 then 1 else (if x<2710 then 0 else 2))) else (if x<3180 then (if x<3118 then 2 else (if x<3158 then 1 else 1)) else (if x<3282 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10030 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2800,3118,3158,3180,3186,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10030 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10030 48 4
  · have he : independentCachedBranchMembers10030.erase 48=independentCachedBranchMembers10028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10028
  · have he : independentCachedBranchMembers10030.filter (independentCachedEdge 48)=independentCachedBranchMembers10029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10029
def independentCachedBranchMembers10031 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1776,2614,2638,2710,2800,3118,3158,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10031 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10031 4 (fun x => (if x<2614 then (if x<1590 then (if x<144 then (if x<72 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1686 then (if x<1614 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3118 then (if x<2710 then (if x<2638 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3158 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10032 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10032 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10032 3242 4
  · have he : independentCachedBranchMembers10032.erase 3242=independentCachedBranchMembers10030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10030
  · have he : independentCachedBranchMembers10032.filter (independentCachedEdge 3242)=independentCachedBranchMembers10031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10031
def independentCachedBranchMembers10033 : Finset ℕ := ([48,72,1590,1614,1708,1714,1738,1748,2666,2676,2710,2800,3180,3186,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10033 4 (fun x => (if x<2666 then (if x<1708 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3180 then (if x<2710 then (if x<2676 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3186 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10034 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10034 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10034 2772 4
  · have he : independentCachedBranchMembers10034.erase 2772=independentCachedBranchMembers10032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10032
  · have he : independentCachedBranchMembers10034.filter (independentCachedEdge 2772)=independentCachedBranchMembers10033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10033
def independentCachedBranchMembers10035 : Finset ℕ := ([144,246,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,3118,3158,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10035 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10035 4 (fun x => (if x<2614 then (if x<1714 then (if x<1686 then (if x<246 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3118 then (if x<2666 then (if x<2638 then 2 else 2) else (if x<2676 then 3 else 3)) else (if x<3180 then (if x<3158 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10036 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10036 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10036 2762 4
  · have he : independentCachedBranchMembers10036.erase 2762=independentCachedBranchMembers10034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10034
  · have he : independentCachedBranchMembers10036.filter (independentCachedEdge 2762)=independentCachedBranchMembers10035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10035
def independentCachedBranchMembers10037 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10037 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10037 3244 5
  · have he : independentCachedBranchMembers10037.erase 3244=independentCachedBranchMembers10025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10025
  · have he : independentCachedBranchMembers10037.filter (independentCachedEdge 3244)=independentCachedBranchMembers10036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10036
def independentCachedBranchMembers10038 : Finset ℕ := ([72,136,238,1590,1614,1678,1706,1716,1740,1746,1768,2606,2646,2668,2674,2710,2732,2738,2762,2800,3126,3150,3178,3188,3214,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10038 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10038 5 (fun x => (if x<2674 then (if x<1716 then (if x<1590 then (if x<136 then 0 else (if x<238 then 1 else 0)) else (if x<1678 then (if x<1614 then 1 else 0) else (if x<1706 then 1 else 2))) else (if x<1768 then (if x<1740 then 2 else (if x<1746 then 2 else 2)) else (if x<2646 then (if x<2606 then 0 else 3) else (if x<2668 then 3 else 0)))) else (if x<3150 then (if x<2738 then (if x<2710 then 1 else (if x<2732 then 4 else 2)) else (if x<2800 then (if x<2762 then 2 else 0) else (if x<3126 then 4 else 3))) else (if x<3214 then (if x<3178 then 3 else (if x<3188 then 0 else 1)) else (if x<3282 then (if x<3276 then 4 else 0) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10039 : Finset ℕ := ([238,1706,1746,1768,2606,2646,2668,2710,2732,3178,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10039 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10039 4 (fun x => (if x<2668 then (if x<1768 then (if x<1706 then 0 else (if x<1746 then 0 else 1)) else (if x<2606 then 1 else (if x<2646 then 0 else 1))) else (if x<3178 then (if x<2710 then 1 else (if x<2732 then 2 else 2)) else (if x<3282 then 0 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10040 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1706,1716,1740,1746,1768,2606,2646,2668,2674,2710,2732,2738,2762,2800,3126,3150,3178,3188,3214,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10040 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10040 48 4
  · have he : independentCachedBranchMembers10040.erase 48=independentCachedBranchMembers10038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10038
  · have he : independentCachedBranchMembers10040.filter (independentCachedEdge 48)=independentCachedBranchMembers10039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10039
def independentCachedBranchMembers10041 : Finset ℕ := ([136,238,1678,1706,1716,1740,1746,1768,2606,2646,2668,2674,3126,3150,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10041 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10041 4 (fun x => (if x<2606 then (if x<1716 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1706 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2668 then (if x<2646 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3178 then (if x<3150 then 2 else 2) else (if x<3188 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10042 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1706,1716,1740,1746,1768,2606,2646,2668,2674,2710,2732,2738,2762,2800,3126,3150,3178,3188,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10042 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10042 3252 4
  · have he : independentCachedBranchMembers10042.erase 3252=independentCachedBranchMembers10040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10040
  · have he : independentCachedBranchMembers10042.filter (independentCachedEdge 3252)=independentCachedBranchMembers10041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10041
def independentCachedBranchMembers10043 : Finset ℕ := ([48,72,1590,1614,1706,1716,1740,1746,2668,2674,2710,2800,3178,3188,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10043 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10043 4 (fun x => (if x<2668 then (if x<1706 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1740 then (if x<1716 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3178 then (if x<2710 then (if x<2674 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3188 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10044 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1706,1716,1740,1746,1768,2606,2646,2668,2674,2710,2732,2738,2762,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10044 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10044 3242 4
  · have he : independentCachedBranchMembers10044.erase 3242=independentCachedBranchMembers10042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10042
  · have he : independentCachedBranchMembers10044.filter (independentCachedEdge 3242)=independentCachedBranchMembers10043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10043
def independentCachedBranchMembers10045 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1768,2606,2646,2710,2800,3126,3150,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10045 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10045 4 (fun x => (if x<2606 then (if x<1590 then (if x<136 then (if x<72 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1678 then (if x<1614 then 0 else 0) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2646 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3150 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10046 : Finset ℕ := ([48,72,136,238,1590,1614,1678,1706,1716,1740,1746,1768,2606,2646,2668,2674,2710,2732,2738,2762,2772,2800,3126,3150,3178,3188,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10046 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10046 2772 4
  · have he : independentCachedBranchMembers10046.erase 2772=independentCachedBranchMembers10044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10044
  · have he : independentCachedBranchMembers10046.filter (independentCachedEdge 2772)=independentCachedBranchMembers10045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10045
def independentCachedBranchMembers10047 : Finset ℕ := ([12,18,48,72,136,144,238,246,1590,1614,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10047 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10047 2770 5
  · have he : independentCachedBranchMembers10047.erase 2770=independentCachedBranchMembers10037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10037
  · have he : independentCachedBranchMembers10047.filter (independentCachedEdge 2770)=independentCachedBranchMembers10046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10046
end EntropyDesigns.QuadraticRefinement
