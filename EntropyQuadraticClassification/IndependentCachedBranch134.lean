/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch133
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7072 : Finset ℕ := ([68,144,1614,1644,1650,1690,1734,1752,2618,2662,2680,2732,2738,2764,2800,3118,3180,3186,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7072 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7072 5 (fun x => (if x<2680 then (if x<1690 then (if x<1614 then (if x<144 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<2618 then 1 else (if x<2662 then 2 else 0)))) else (if x<3118 then (if x<2738 then (if x<2732 then 1 else 2) else (if x<2764 then 0 else (if x<2800 then 1 else 2))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3256 then 2 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7073 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2674,2680,2714,2732,2738,2764,2800,3118,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7073 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7073 2674 5
  · have he : independentCachedBranchMembers7073.erase 2674=independentCachedBranchMembers7071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7071
  · have he : independentCachedBranchMembers7073.filter (independentCachedEdge 2674)=independentCachedBranchMembers7072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7072
def independentCachedBranchMembers7074 : Finset ℕ := ([48,250,1594,1644,1650,1734,1752,1776,2638,2662,2680,2714,2732,2738,2764,3162,3180,3186,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7074 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7074 5 (fun x => (if x<2680 then (if x<1734 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1776 then (if x<1752 then 1 else 1) else (if x<2638 then 0 else (if x<2662 then 2 else 1)))) else (if x<3162 then (if x<2732 then (if x<2714 then 0 else 2) else (if x<2738 then 2 else (if x<2764 then 0 else 1))) else (if x<3186 then (if x<3180 then 2 else 2) else (if x<3214 then 0 else (if x<3256 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7075 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2668,2674,2680,2714,2732,2738,2764,2800,3118,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7075 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7075 2668 5
  · have he : independentCachedBranchMembers7075.erase 2668=independentCachedBranchMembers7073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7073
  · have he : independentCachedBranchMembers7075.filter (independentCachedEdge 2668)=independentCachedBranchMembers7074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7074
def independentCachedBranchMembers7076 : Finset ℕ := ([18,250,1594,1614,1650,1690,1708,1752,2618,2638,2674,2680,2714,2732,3118,3162,3174,3180,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7076 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7076 5 (fun x => (if x<2680 then (if x<1690 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1614 then 0 else (if x<1650 then 1 else 1))) else (if x<2618 then (if x<1708 then 1 else (if x<1752 then 2 else 2)) else (if x<2638 then 3 else (if x<2674 then 3 else 0)))) else (if x<3174 then (if x<2732 then (if x<2714 then 4 else 0) else (if x<3118 then 3 else (if x<3162 then 2 else 0))) else (if x<3250 then (if x<3180 then 1 else (if x<3214 then 4 else 1)) else (if x<3256 then 0 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7077 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2668,2674,2680,2714,2732,2738,2764,2800,3118,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7077 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7077 3150 5
  · have he : independentCachedBranchMembers7077.erase 3150=independentCachedBranchMembers7075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7075
  · have he : independentCachedBranchMembers7077.filter (independentCachedEdge 3150)=independentCachedBranchMembers7076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7076
def independentCachedBranchMembers7078 : Finset ℕ := ([12,144,1594,1614,1644,1708,1752,1776,2618,2638,2662,2668,2732,2800,3118,3162,3186,3192,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7078 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7078 5 (fun x => (if x<2668 then (if x<1708 then (if x<1594 then (if x<144 then 0 else 0) else (if x<1614 then 1 else (if x<1644 then 0 else 1))) else (if x<2618 then (if x<1752 then 2 else (if x<1776 then 1 else 2)) else (if x<2638 then 3 else (if x<2662 then 3 else 4)))) else (if x<3186 then (if x<2800 then (if x<2732 then 0 else 3) else (if x<3118 then 0 else (if x<3162 then 0 else 3))) else (if x<3256 then (if x<3192 then 2 else (if x<3250 then 1 else 0)) else (if x<3276 then 2 else (if x<3300 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7079 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2668,2674,2680,2714,2732,2738,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7079 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7079 3130 5
  · have he : independentCachedBranchMembers7079.erase 3130=independentCachedBranchMembers7077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7077
  · have he : independentCachedBranchMembers7079.filter (independentCachedEdge 3130)=independentCachedBranchMembers7078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7078
def independentCachedBranchMembers7080 : Finset ℕ := ([12,18,144,250,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2764,3118,3162,3180,3186,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7080 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7080 5 (fun x => (if x<1776 then (if x<1650 then (if x<144 then (if x<18 then 0 else 0) else (if x<250 then 1 else (if x<1644 then 1 else 0))) else (if x<1714 then (if x<1690 then 0 else (if x<1708 then 1 else 2)) else (if x<1734 then 2 else (if x<1752 then 2 else 2)))) else (if x<2764 then (if x<2638 then (if x<2618 then 1 else 3) else (if x<2662 then 3 else (if x<2680 then 4 else 4))) else (if x<3180 then (if x<3118 then 0 else (if x<3162 then 3 else 3)) else (if x<3186 then 4 else (if x<3250 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7081 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7081 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7081 2758 5
  · have he : independentCachedBranchMembers7081.erase 2758=independentCachedBranchMembers7079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7079
  · have he : independentCachedBranchMembers7081.filter (independentCachedEdge 2758)=independentCachedBranchMembers7080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7080
def independentCachedBranchMembers7082 : Finset ℕ := ([12,48,68,144,1644,1714,1734,1776,2618,2638,2674,2680,2714,2732,3118,3162,3174,3180,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7082 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7082 5 (fun x => (if x<2680 then (if x<1714 then (if x<68 then (if x<48 then 0 else 0) else (if x<144 then 1 else (if x<1644 then 1 else 1))) else (if x<2618 then (if x<1734 then 0 else (if x<1776 then 2 else 2)) else (if x<2638 then 3 else (if x<2674 then 0 else 0)))) else (if x<3174 then (if x<2732 then (if x<2714 then 2 else 1) else (if x<3118 then 3 else (if x<3162 then 3 else 3))) else (if x<3250 then (if x<3180 then 1 else (if x<3214 then 4 else 2)) else (if x<3256 then 1 else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7083 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7083 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7083 2650 5
  · have he : independentCachedBranchMembers7083.erase 2650=independentCachedBranchMembers7081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7081
  · have he : independentCachedBranchMembers7083.filter (independentCachedEdge 2650)=independentCachedBranchMembers7082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7082
def independentCachedBranchMembers7084 : Finset ℕ := ([18,48,68,250,1650,1690,1714,1734,2618,2638,2662,2668,2732,2800,3118,3162,3186,3192,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7084 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7084 5 (fun x => (if x<2668 then (if x<1690 then (if x<68 then (if x<48 then 0 else 1) else (if x<250 then 0 else (if x<1650 then 1 else 1))) else (if x<2618 then (if x<1714 then 0 else (if x<1734 then 2 else 2)) else (if x<2638 then 0 else (if x<2662 then 2 else 3)))) else (if x<3186 then (if x<2800 then (if x<2732 then 0 else 3) else (if x<3118 then 1 else (if x<3162 then 3 else 4))) else (if x<3256 then (if x<3192 then 3 else (if x<3250 then 1 else 0)) else (if x<3276 then 2 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7085 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7085 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7085 2606 5
  · have he : independentCachedBranchMembers7085.erase 2606=independentCachedBranchMembers7083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7083
  · have he : independentCachedBranchMembers7085.filter (independentCachedEdge 2606)=independentCachedBranchMembers7084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7084
def independentCachedBranchMembers7086 : Finset ℕ := ([48,68,1644,1650,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2764,3130,3150,3174,3192,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7086 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7086 5 (fun x => (if x<2662 then (if x<1714 then (if x<1650 then (if x<68 then 0 else (if x<1644 then 0 else 1)) else (if x<1690 then 1 else (if x<1708 then 2 else 2))) else (if x<1776 then (if x<1734 then 0 else (if x<1752 then 0 else 1)) else (if x<2618 then 2 else (if x<2638 then 0 else 0)))) else (if x<3192 then (if x<3130 then (if x<2680 then 1 else (if x<2764 then 1 else 1)) else (if x<3150 then 3 else (if x<3174 then 3 else 4))) else (if x<3276 then (if x<3214 then 4 else (if x<3256 then 2 else 0)) else (if x<3282 then 0 else (if x<3300 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7087 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1746,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7087 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7087 1746 5
  · have he : independentCachedBranchMembers7087.erase 1746=independentCachedBranchMembers7085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7085
  · have he : independentCachedBranchMembers7087.filter (independentCachedEdge 1746)=independentCachedBranchMembers7086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7086
def independentCachedBranchMembers7088 : Finset ℕ := ([144,250,1594,1614,1644,1650,1708,1714,1734,1752,2606,2650,2662,2680,2714,2764,2800,3118,3162,3174,3192,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7088 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7088 5 (fun x => (if x<2662 then (if x<1708 then (if x<1614 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 1 else (if x<1650 then 2 else 2))) else (if x<1752 then (if x<1714 then 1 else (if x<1734 then 0 else 2)) else (if x<2606 then 0 else (if x<2650 then 1 else 1)))) else (if x<3162 then (if x<2764 then (if x<2680 then 2 else (if x<2714 then 2 else 0)) else (if x<2800 then 1 else (if x<3118 then 0 else 3))) else (if x<3256 then (if x<3174 then 3 else (if x<3192 then 4 else 4)) else (if x<3276 then 0 else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7089 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1734,1740,1746,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7089 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7089 1740 5
  · have he : independentCachedBranchMembers7089.erase 1740=independentCachedBranchMembers7087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7087
  · have he : independentCachedBranchMembers7089.filter (independentCachedEdge 1740)=independentCachedBranchMembers7088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7088
def independentCachedBranchMembers7090 : Finset ℕ := ([12,18,1594,1614,1690,1708,1714,1734,1752,1776,2606,2650,2668,2674,2764,3118,3162,3180,3186,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7090 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7090 5 (fun x => (if x<2668 then (if x<1714 then (if x<1614 then (if x<18 then 0 else (if x<1594 then 0 else 1)) else (if x<1690 then 1 else (if x<1708 then 2 else 0))) else (if x<1776 then (if x<1734 then 0 else (if x<1752 then 2 else 1)) else (if x<2606 then 2 else (if x<2650 then 1 else 1)))) else (if x<3186 then (if x<3118 then (if x<2674 then 0 else (if x<2764 then 0 else 1)) else (if x<3162 then 3 else (if x<3180 then 3 else 4))) else (if x<3276 then (if x<3214 then 4 else (if x<3256 then 2 else 2)) else (if x<3282 then 0 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7091 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1708,1714,1720,1734,1740,1746,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7091 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7091 1720 5
  · have he : independentCachedBranchMembers7091.erase 1720=independentCachedBranchMembers7089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7089
  · have he : independentCachedBranchMembers7091.filter (independentCachedEdge 1720)=independentCachedBranchMembers7090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7090
def independentCachedBranchMembers7092 : Finset ℕ := ([12,18,48,68,144,250,1708,1714,1734,1752,2618,2638,2668,2674,2714,2764,2800,3130,3150,3180,3186,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7092 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7092 5 (fun x => (if x<2668 then (if x<1708 then (if x<68 then (if x<18 then 0 else (if x<48 then 0 else 1)) else (if x<144 then 1 else (if x<250 then 2 else 2))) else (if x<1752 then (if x<1714 then 0 else (if x<1734 then 0 else 1)) else (if x<2618 then 2 else (if x<2638 then 1 else 1)))) else (if x<3150 then (if x<2764 then (if x<2674 then 0 else (if x<2714 then 0 else 2)) else (if x<2800 then 3 else (if x<3130 then 2 else 3))) else (if x<3256 then (if x<3180 then 3 else (if x<3186 then 4 else 4)) else (if x<3276 then 1 else (if x<3282 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7093 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1702,1708,1714,1720,1734,1740,1746,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7093 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7093 1702 5
  · have he : independentCachedBranchMembers7093.erase 1702=independentCachedBranchMembers7091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7091
  · have he : independentCachedBranchMembers7093.filter (independentCachedEdge 1702)=independentCachedBranchMembers7092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7092
def independentCachedBranchMembers7094 : Finset ℕ := ([12,48,1594,1644,1690,1702,1708,1734,1740,1776,2606,2638,2674,2680,2738,3118,3150,3186,3192,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7094 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7094 5 (fun x => (if x<2674 then (if x<1708 then (if x<1644 then (if x<48 then 0 else (if x<1594 then 0 else 1)) else (if x<1690 then 1 else (if x<1702 then 2 else 1))) else (if x<1776 then (if x<1734 then 2 else (if x<1740 then 2 else 0)) else (if x<2606 then 0 else (if x<2638 then 1 else 0)))) else (if x<3192 then (if x<3118 then (if x<2680 then 0 else (if x<2738 then 1 else 1)) else (if x<3150 then 3 else (if x<3186 then 4 else 3))) else (if x<3256 then (if x<3214 then 4 else (if x<3250 then 0 else 0)) else (if x<3282 then 2 else (if x<3300 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7095 : Finset ℕ := ([12,1644,1702,1708,1734,1740,2606,2638,3118,3150,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7095 4 (fun x => (if x<2606 then (if x<1708 then (if x<1644 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1740 then 2 else 1))) else (if x<3150 then (if x<2638 then 0 else (if x<3118 then 3 else 3)) else (if x<3214 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7096 : Finset ℕ := ([12,48,250,1594,1644,1690,1702,1708,1734,1740,1776,2606,2638,2674,2680,2738,3118,3150,3186,3192,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7096 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7096 250 4
  · have he : independentCachedBranchMembers7096.erase 250=independentCachedBranchMembers7094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7094
  · have he : independentCachedBranchMembers7096.filter (independentCachedEdge 250)=independentCachedBranchMembers7095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7095
def independentCachedBranchMembers7097 : Finset ℕ := ([48,1594,1702,1708,1734,1740,2674,2680,3186,3192,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7097 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7097 4 (fun x => (if x<2674 then (if x<1708 then (if x<1594 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1740 then 2 else 1))) else (if x<3192 then (if x<2680 then 0 else (if x<3186 then 3 else 3)) else (if x<3214 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7098 : Finset ℕ := ([12,48,144,250,1594,1644,1690,1702,1708,1734,1740,1776,2606,2638,2674,2680,2738,3118,3150,3186,3192,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7098 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7098 144 4
  · have he : independentCachedBranchMembers7098.erase 144=independentCachedBranchMembers7096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7096
  · have he : independentCachedBranchMembers7098.filter (independentCachedEdge 144)=independentCachedBranchMembers7097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7097
def independentCachedBranchMembers7099 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7099 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7099 1764 5
  · have he : independentCachedBranchMembers7099.erase 1764=independentCachedBranchMembers7093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7093
  · have he : independentCachedBranchMembers7099.filter (independentCachedEdge 1764)=independentCachedBranchMembers7098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7098
def independentCachedBranchMembers7100 : Finset ℕ := ([18,68,1614,1650,1690,1702,1708,1734,1740,1776,2618,2650,2662,2668,2738,3130,3162,3174,3180,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7100 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7100 5 (fun x => (if x<2662 then (if x<1708 then (if x<1650 then (if x<68 then 0 else (if x<1614 then 0 else 1)) else (if x<1690 then 1 else (if x<1702 then 0 else 1))) else (if x<1776 then (if x<1734 then 2 else (if x<1740 then 2 else 0)) else (if x<2618 then 2 else (if x<2650 then 0 else 1)))) else (if x<3180 then (if x<3130 then (if x<2668 then 1 else (if x<2738 then 0 else 1)) else (if x<3162 then 3 else (if x<3174 then 4 else 3))) else (if x<3256 then (if x<3214 then 4 else (if x<3250 then 2 else 0)) else (if x<3282 then 2 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7101 : Finset ℕ := ([68,1614,1702,1708,1734,1740,2662,2668,3174,3180,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7101 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7101 4 (fun x => (if x<2662 then (if x<1708 then (if x<1614 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1740 then 2 else 1))) else (if x<3180 then (if x<2668 then 0 else (if x<3174 then 3 else 3)) else (if x<3214 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7102 : Finset ℕ := ([18,68,250,1614,1650,1690,1702,1708,1734,1740,1776,2618,2650,2662,2668,2738,3130,3162,3174,3180,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7102 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7102 250 4
  · have he : independentCachedBranchMembers7102.erase 250=independentCachedBranchMembers7100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7100
  · have he : independentCachedBranchMembers7102.filter (independentCachedEdge 250)=independentCachedBranchMembers7101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7101
def independentCachedBranchMembers7103 : Finset ℕ := ([18,1650,1702,1708,1734,1740,2618,2650,3130,3162,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7103 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7103 4 (fun x => (if x<2618 then (if x<1708 then (if x<1650 then 0 else (if x<1702 then 0 else 1)) else (if x<1734 then 2 else (if x<1740 then 2 else 1))) else (if x<3162 then (if x<2650 then 0 else (if x<3130 then 3 else 3)) else (if x<3214 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
