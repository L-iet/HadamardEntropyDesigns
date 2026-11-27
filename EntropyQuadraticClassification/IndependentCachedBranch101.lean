/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch100
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6016 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6016 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6016 40 4
  · have he : independentCachedBranchMembers6016.erase 40=independentCachedBranchMembers6014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6014
  · have he : independentCachedBranchMembers6016.filter (independentCachedEdge 40)=independentCachedBranchMembers6015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6015
def independentCachedBranchMembers6017 : Finset ℕ := ([80,250,1652,1714,1720,1748,2674,2776,3130,3158,3164,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6017 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6017 4 (fun x => (if x<2674 then (if x<1714 then (if x<250 then 0 else (if x<1652 then 0 else 1)) else (if x<1720 then 1 else (if x<1748 then 2 else 2))) else (if x<3158 then (if x<2776 then 0 else (if x<3130 then 0 else 2)) else (if x<3164 then 2 else (if x<3226 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6018 : Finset ℕ := ([40,80,130,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6018 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6018 238 4
  · have he : independentCachedBranchMembers6018.erase 238=independentCachedBranchMembers6016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6016
  · have he : independentCachedBranchMembers6018.filter (independentCachedEdge 238)=independentCachedBranchMembers6017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6017
def independentCachedBranchMembers6019 : Finset ℕ := ([40,130,1642,1702,1714,1748,2668,2758,3118,3130,3164,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6019 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6019 4 (fun x => (if x<2668 then (if x<1702 then (if x<130 then 0 else (if x<1642 then 0 else 1)) else (if x<1714 then 1 else (if x<1748 then 2 else 2))) else (if x<3130 then (if x<2758 then 0 else (if x<3118 then 0 else 1)) else (if x<3164 then 2 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6020 : Finset ℕ := ([40,80,130,136,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6020 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6020 136 4
  · have he : independentCachedBranchMembers6020.erase 136=independentCachedBranchMembers6018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6018
  · have he : independentCachedBranchMembers6020.filter (independentCachedEdge 136)=independentCachedBranchMembers6019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6019
def independentCachedBranchMembers6021 : Finset ℕ := ([80,250,1642,1702,1708,1738,2674,2776,3118,3214,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6021 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6021 4 (fun x => (if x<2674 then (if x<1702 then (if x<250 then 0 else (if x<1642 then 0 else 1)) else (if x<1708 then 1 else (if x<1738 then 2 else 2))) else (if x<3214 then (if x<2776 then 0 else (if x<3118 then 0 else 1)) else (if x<3298 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6022 : Finset ℕ := ([40,68,80,130,136,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6022 68 4
  · have he : independentCachedBranchMembers6022.erase 68=independentCachedBranchMembers6020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6020
  · have he : independentCachedBranchMembers6022.filter (independentCachedEdge 68)=independentCachedBranchMembers6021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6021
def independentCachedBranchMembers6023 : Finset ℕ := ([40,130,1652,1708,1720,1738,2668,2758,3158,3214,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6023 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6023 4 (fun x => (if x<2668 then (if x<1708 then (if x<130 then 0 else (if x<1652 then 0 else 1)) else (if x<1720 then 1 else (if x<1738 then 2 else 2))) else (if x<3214 then (if x<2758 then 0 else (if x<3158 then 0 else 1)) else (if x<3226 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6024 : Finset ℕ := ([34,40,68,80,130,136,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6024 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6024 34 4
  · have he : independentCachedBranchMembers6024.erase 34=independentCachedBranchMembers6022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6022
  · have he : independentCachedBranchMembers6024.filter (independentCachedEdge 34)=independentCachedBranchMembers6023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6023
def independentCachedBranchMembers6025 : Finset ℕ := ([34,40,68,80,130,136,238,250,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6025 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6025 4 (fun x => (if x<3118 then (if x<130 then (if x<68 then (if x<40 then 0 else 1) else (if x<80 then 0 else 1)) else (if x<238 then (if x<136 then 1 else 0) else (if x<250 then 0 else 1))) else (if x<3214 then (if x<3158 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)) else (if x<3298 then (if x<3226 then 3 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6026 : Finset ℕ := ([34,40,68,80,130,136,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2740,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6026 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6026 2740 4
  · have he : independentCachedBranchMembers6026.erase 2740=independentCachedBranchMembers6024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6024
  · have he : independentCachedBranchMembers6026.filter (independentCachedEdge 2740)=independentCachedBranchMembers6025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6025
def independentCachedBranchMembers6027 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6027 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6027 3102 5
  · have he : independentCachedBranchMembers6027.erase 3102=independentCachedBranchMembers6011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6011
  · have he : independentCachedBranchMembers6027.filter (independentCachedEdge 3102)=independentCachedBranchMembers6026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6026
def independentCachedBranchMembers6028 : Finset ℕ := ([1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1776,2606,2618,2646,2652,2668,2674,2702,2714,2740,2758,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6028 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6028 5 (fun x => (if x<2618 then (if x<1714 then (if x<1686 then (if x<1642 then 0 else (if x<1652 then 1 else 0)) else (if x<1702 then 0 else (if x<1708 then 1 else 2))) else (if x<1748 then (if x<1720 then 2 else (if x<1738 then 0 else 2)) else (if x<1776 then 2 else (if x<2606 then 1 else 1)))) else (if x<2714 then (if x<2668 then (if x<2646 then 3 else (if x<2652 then 0 else 3)) else (if x<2674 then 4 else (if x<2702 then 4 else 3))) else (if x<2776 then (if x<2740 then 0 else (if x<2758 then 0 else 4)) else (if x<2786 then 4 else (if x<2792 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6029 : Finset ℕ := ([1652,1708,1720,1738,2646,2674,2702,2714,2776,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6029 4 (fun x => (if x<2674 then (if x<1720 then (if x<1708 then 0 else 0) else (if x<1738 then 1 else (if x<2646 then 1 else 0))) else (if x<2714 then (if x<2702 then 2 else 0) else (if x<2776 then 1 else (if x<2792 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6030 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1776,2606,2618,2646,2652,2668,2674,2702,2714,2740,2758,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6030 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6030 1596 4
  · have he : independentCachedBranchMembers6030.erase 1596=independentCachedBranchMembers6028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6028
  · have he : independentCachedBranchMembers6030.filter (independentCachedEdge 1596)=independentCachedBranchMembers6029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6029
def independentCachedBranchMembers6031 : Finset ℕ := ([1626,1652,1702,1708,1748,1776,2606,2646,2652,2674,2702,2776] : List ℕ).toFinset
theorem independentCachedBranchBound6031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6031 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6031 4 (fun x => (if x<2606 then (if x<1708 then (if x<1652 then 0 else (if x<1702 then 0 else 1)) else (if x<1748 then 2 else (if x<1776 then 1 else 2))) else (if x<2674 then (if x<2646 then 1 else (if x<2652 then 0 else 1)) else (if x<2702 then 2 else (if x<2776 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6032 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2740,2758,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6032 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6032 1764 4
  · have he : independentCachedBranchMembers6032.erase 1764=independentCachedBranchMembers6030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6030
  · have he : independentCachedBranchMembers6032.filter (independentCachedEdge 1764)=independentCachedBranchMembers6031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6031
def independentCachedBranchMembers6033 : Finset ℕ := ([1596,1642,1686,1708,1720,1748,2606,2618,2646,2668,2758,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6033 4 (fun x => (if x<2606 then (if x<1708 then (if x<1642 then 0 else (if x<1686 then 0 else 1)) else (if x<1720 then 1 else (if x<1748 then 2 else 2))) else (if x<2668 then (if x<2618 then 0 else (if x<2646 then 2 else 1)) else (if x<2758 then 1 else (if x<2792 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6034 : Finset ℕ := ([1596,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2740,2758,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6034 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6034 1692 4
  · have he : independentCachedBranchMembers6034.erase 1692=independentCachedBranchMembers6032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6032
  · have he : independentCachedBranchMembers6034.filter (independentCachedEdge 1692)=independentCachedBranchMembers6033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6033
def independentCachedBranchMembers6035 : Finset ℕ := ([1626,1642,1714,1720,1738,1776,2618,2674,2714,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6035 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6035 4 (fun x => (if x<2618 then (if x<1720 then (if x<1642 then 0 else (if x<1714 then 1 else 0)) else (if x<1738 then 1 else (if x<1776 then 2 else 2))) else (if x<2776 then (if x<2674 then 0 else (if x<2714 then 3 else 3)) else (if x<2786 then 2 else (if x<2792 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6036 : Finset ℕ := ([1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2740,2758,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6036 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6036 1614 4
  · have he : independentCachedBranchMembers6036.erase 1614=independentCachedBranchMembers6034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6034
  · have he : independentCachedBranchMembers6036.filter (independentCachedEdge 1614)=independentCachedBranchMembers6035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6035
def independentCachedBranchMembers6037 : Finset ℕ := ([1596,1652,1686,1702,1714,1738,2652,2668,2702,2714,2758,2786] : List ℕ).toFinset
theorem independentCachedBranchBound6037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6037 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6037 4 (fun x => (if x<2652 then (if x<1702 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<1714 then 1 else (if x<1738 then 2 else 2))) else (if x<2714 then (if x<2668 then 1 else (if x<2702 then 0 else 1)) else (if x<2758 then 2 else (if x<2786 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6038 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2740,2758,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6038 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6038 1590 4
  · have he : independentCachedBranchMembers6038.erase 1590=independentCachedBranchMembers6036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6036
  · have he : independentCachedBranchMembers6038.filter (independentCachedEdge 1590)=independentCachedBranchMembers6037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6037
def independentCachedBranchMembers6039 : Finset ℕ := ([1590,1596,1614,1626,1686,1692,1764,1776,2606,2618,2646,2652,2702,2714,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6039 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6039 4 (fun x => (if x<2606 then (if x<1686 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1626 then 0 else 1)) else (if x<1764 then (if x<1692 then 1 else 0) else (if x<1776 then 0 else 1))) else (if x<2702 then (if x<2646 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<2786 then (if x<2714 then 3 else 2) else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6040 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6040 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6040 2730 4
  · have he : independentCachedBranchMembers6040.erase 2730=independentCachedBranchMembers6038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6038
  · have he : independentCachedBranchMembers6040.filter (independentCachedEdge 2730)=independentCachedBranchMembers6039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6039
def independentCachedBranchMembers6041 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6041 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6041 3072 5
  · have he : independentCachedBranchMembers6041.erase 3072=independentCachedBranchMembers6027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6027
  · have he : independentCachedBranchMembers6041.filter (independentCachedEdge 3072)=independentCachedBranchMembers6040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6040
def independentCachedBranchMembers6042 : Finset ℕ := ([238,1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6042 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6042 5 (fun x => (if x<2714 then (if x<1702 then (if x<1642 then (if x<1590 then 0 else (if x<1614 then 1 else 0)) else (if x<1652 then 1 else (if x<1692 then 2 else 2))) else (if x<2606 then (if x<1720 then 0 else (if x<1764 then 1 else 1)) else (if x<2668 then (if x<2646 then 0 else 3) else (if x<2674 then 3 else 2)))) else (if x<3174 then (if x<2786 then (if x<2758 then 2 else (if x<2776 then 0 else 3)) else (if x<3130 then 3 else (if x<3164 then 1 else 3))) else (if x<3252 then (if x<3214 then 0 else (if x<3242 then 0 else 4)) else (if x<3282 then (if x<3276 then 1 else 4) else (if x<3304 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6043 : Finset ℕ := ([1614,1642,1702,1764,2606,2668,2758,2786,3130,3164,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6043 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6043 4 (fun x => (if x<2758 then (if x<1764 then (if x<1642 then 0 else (if x<1702 then 1 else 0)) else (if x<2606 then 1 else (if x<2668 then 0 else 1))) else (if x<3164 then (if x<2786 then 0 else (if x<3130 then 1 else 2)) else (if x<3252 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6044 : Finset ℕ := ([136,238,1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6044 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6044 136 4
  · have he : independentCachedBranchMembers6044.erase 136=independentCachedBranchMembers6042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6042
  · have he : independentCachedBranchMembers6044.filter (independentCachedEdge 136)=independentCachedBranchMembers6043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6043
def independentCachedBranchMembers6045 : Finset ℕ := ([1590,1642,1692,1702,2606,2674,2776,2786,3214,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6045 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6045 4 (fun x => (if x<2776 then (if x<1702 then (if x<1642 then 0 else (if x<1692 then 0 else 1)) else (if x<2606 then 1 else (if x<2674 then 0 else 0))) else (if x<3252 then (if x<2786 then 1 else (if x<3214 then 1 else 2)) else (if x<3282 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6046 : Finset ℕ := ([68,136,238,1590,1614,1642,1652,1692,1702,1720,1764,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6046 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6046 68 4
  · have he : independentCachedBranchMembers6046.erase 68=independentCachedBranchMembers6044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6044
  · have he : independentCachedBranchMembers6046.filter (independentCachedEdge 68)=independentCachedBranchMembers6045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6045
def independentCachedBranchMembers6047 : Finset ℕ := ([1614,1652,1720,1764,2646,2668,2714,2758,3214,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6047 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6047 4 (fun x => (if x<2714 then (if x<1764 then (if x<1652 then 0 else (if x<1720 then 0 else 1)) else (if x<2646 then 1 else (if x<2668 then 0 else 0))) else (if x<3252 then (if x<2758 then 1 else (if x<3214 then 1 else 2)) else (if x<3282 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
