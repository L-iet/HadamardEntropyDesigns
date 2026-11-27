/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch135
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7136 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7136 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7136 12 4
  · have he : independentCachedBranchMembers7136.erase 12=independentCachedBranchMembers7134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7134
  · have he : independentCachedBranchMembers7136.filter (independentCachedEdge 12)=independentCachedBranchMembers7135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7135
def independentCachedBranchMembers7137 : Finset ℕ := ([144,250,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,3118,3162,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7137 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7137 4 (fun x => (if x<2618 then (if x<1720 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3118 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3162 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7138 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2764,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7138 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7138 2764 4
  · have he : independentCachedBranchMembers7138.erase 2764=independentCachedBranchMembers7136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7136
  · have he : independentCachedBranchMembers7138.filter (independentCachedEdge 2764)=independentCachedBranchMembers7137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7137
def independentCachedBranchMembers7139 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3238,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7139 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7139 3238 5
  · have he : independentCachedBranchMembers7139.erase 3238=independentCachedBranchMembers7123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7123
  · have he : independentCachedBranchMembers7139.filter (independentCachedEdge 3238)=independentCachedBranchMembers7138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7138
def independentCachedBranchMembers7140 : Finset ℕ := ([12,48,132,238,1614,1650,1690,1702,1708,1734,1740,1776,2606,2638,2674,2680,2714,2732,2758,2764,2800,3130,3162,3174,3180,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7140 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7140 5 (fun x => (if x<2680 then (if x<1702 then (if x<238 then (if x<48 then 0 else (if x<132 then 0 else 1)) else (if x<1650 then (if x<1614 then 1 else 0) else (if x<1690 then 0 else 2))) else (if x<1776 then (if x<1734 then (if x<1708 then 1 else 2) else (if x<1740 then 2 else 1)) else (if x<2638 then (if x<2606 then 2 else 3) else (if x<2674 then 4 else 3)))) else (if x<3162 then (if x<2758 then (if x<2714 then 4 else (if x<2732 then 3 else 1)) else (if x<2800 then (if x<2764 then 1 else 0) else (if x<3130 then 0 else 3))) else (if x<3250 then (if x<3180 then (if x<3174 then 4 else 3) else (if x<3214 then 4 else 0)) else (if x<3282 then (if x<3256 then 0 else 2) else (if x<3300 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7141 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7141 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7141 3226 5
  · have he : independentCachedBranchMembers7141.erase 3226=independentCachedBranchMembers7139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7139
  · have he : independentCachedBranchMembers7141.filter (independentCachedEdge 3226)=independentCachedBranchMembers7140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7140
def independentCachedBranchMembers7142 : Finset ℕ := ([12,48,144,250,1614,1650,1678,1714,1720,1746,1752,1764,2618,2650,2662,2668,2714,2732,2758,2764,2800,3118,3150,3186,3192,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7142 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7142 5 (fun x => (if x<2668 then (if x<1714 then (if x<250 then (if x<48 then 0 else (if x<144 then 0 else 1)) else (if x<1650 then (if x<1614 then 1 else 0) else (if x<1678 then 0 else 2))) else (if x<1764 then (if x<1746 then (if x<1720 then 1 else 2) else (if x<1752 then 2 else 1)) else (if x<2650 then (if x<2618 then 2 else 3) else (if x<2662 then 4 else 3)))) else (if x<3150 then (if x<2758 then (if x<2714 then 4 else (if x<2732 then 1 else 2)) else (if x<2800 then (if x<2764 then 2 else 0) else (if x<3118 then 0 else 3))) else (if x<3250 then (if x<3192 then (if x<3186 then 4 else 3) else (if x<3214 then 4 else 0)) else (if x<3282 then (if x<3256 then 0 else 1) else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7143 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7143 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7143 2788 5
  · have he : independentCachedBranchMembers7143.erase 2788=independentCachedBranchMembers7141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7141
  · have he : independentCachedBranchMembers7143.filter (independentCachedEdge 2788)=independentCachedBranchMembers7142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7142
def independentCachedBranchMembers7144 : Finset ℕ := ([18,48,68,132,238,1594,1614,1644,1650,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2714,2764,2800,3130,3150,3180,3186,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7144 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7144 5 (fun x => (if x<1764 then (if x<1644 then (if x<132 then (if x<48 then 0 else (if x<68 then 1 else 0)) else (if x<1594 then (if x<238 then 1 else 2) else (if x<1614 then 0 else 2))) else (if x<1708 then (if x<1650 then 0 else (if x<1678 then 1 else 3)) else (if x<1734 then (if x<1714 then 2 else 3) else (if x<1752 then 1 else 3)))) else (if x<2800 then (if x<2662 then (if x<2606 then 3 else (if x<2650 then 2 else 4)) else (if x<2714 then (if x<2680 then 4 else 1) else (if x<2764 then 0 else 0))) else (if x<3180 then (if x<3130 then 3 else (if x<3150 then 1 else 4)) else (if x<3214 then (if x<3186 then 2 else 4) else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7145 : Finset ℕ := ([68,132,1594,1734,1752,1764,2650,2662,2680,2714,3130,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7145 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7145 4 (fun x => (if x<2650 then (if x<1734 then (if x<132 then 0 else (if x<1594 then 1 else 0)) else (if x<1752 then 1 else (if x<1764 then 2 else 2))) else (if x<2714 then (if x<2662 then 2 else (if x<2680 then 2 else 1)) else (if x<3130 then 0 else (if x<3300 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7146 : Finset ℕ := ([12,18,48,68,132,238,1594,1614,1644,1650,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2714,2764,2800,3130,3150,3180,3186,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7146 12 4
  · have he : independentCachedBranchMembers7146.erase 12=independentCachedBranchMembers7144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7144
  · have he : independentCachedBranchMembers7146.filter (independentCachedEdge 12)=independentCachedBranchMembers7145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7145
def independentCachedBranchMembers7147 : Finset ℕ := ([132,238,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,3130,3150,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7147 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7147 4 (fun x => (if x<2606 then (if x<1714 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3130 then (if x<2662 then (if x<2650 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3150 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7148 : Finset ℕ := ([12,18,48,68,132,238,1594,1614,1644,1650,1678,1708,1714,1734,1752,1764,2606,2650,2662,2680,2714,2764,2800,3130,3150,3180,3186,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7148 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7148 3250 4
  · have he : independentCachedBranchMembers7148.erase 3250=independentCachedBranchMembers7146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7146
  · have he : independentCachedBranchMembers7148.filter (independentCachedEdge 3250)=independentCachedBranchMembers7147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7147
def independentCachedBranchMembers7149 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7149 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7149 2776 5
  · have he : independentCachedBranchMembers7149.erase 2776=independentCachedBranchMembers7143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7143
  · have he : independentCachedBranchMembers7149.filter (independentCachedEdge 2776)=independentCachedBranchMembers7148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7148
def independentCachedBranchMembers7150 : Finset ℕ := ([18,68,144,250,1594,1644,1678,1714,1720,1746,1752,1764,2606,2638,2674,2680,2714,2732,2758,2764,2800,3130,3162,3174,3180,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7150 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7150 5 (fun x => (if x<2680 then (if x<1714 then (if x<250 then (if x<68 then 0 else (if x<144 then 0 else 1)) else (if x<1644 then (if x<1594 then 1 else 0) else (if x<1678 then 0 else 2))) else (if x<1764 then (if x<1746 then (if x<1720 then 1 else 2) else (if x<1752 then 2 else 1)) else (if x<2638 then (if x<2606 then 2 else 3) else (if x<2674 then 4 else 3)))) else (if x<3162 then (if x<2758 then (if x<2714 then 4 else (if x<2732 then 0 else 2)) else (if x<2800 then (if x<2764 then 2 else 0) else (if x<3130 then 1 else 3))) else (if x<3250 then (if x<3180 then (if x<3174 then 4 else 3) else (if x<3214 then 4 else 3)) else (if x<3282 then (if x<3256 then 0 else 1) else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7151 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7151 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7151 2702 5
  · have he : independentCachedBranchMembers7151.erase 2702=independentCachedBranchMembers7149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7149
  · have he : independentCachedBranchMembers7151.filter (independentCachedEdge 2702)=independentCachedBranchMembers7150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7150
def independentCachedBranchMembers7152 : Finset ℕ := ([144,250,1594,1614,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2800,3118,3162,3180,3186,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7152 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7152 5 (fun x => (if x<2680 then (if x<1714 then (if x<1614 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1690 then 1 else (if x<1708 then 0 else 1))) else (if x<1776 then (if x<1734 then 2 else (if x<1752 then 2 else 1)) else (if x<2638 then (if x<2618 then 0 else 2) else (if x<2662 then 2 else 3)))) else (if x<3180 then (if x<2738 then (if x<2714 then 3 else (if x<2732 then 4 else 3)) else (if x<3118 then (if x<2800 then 0 else 4) else (if x<3162 then 1 else 1))) else (if x<3256 then (if x<3186 then 3 else (if x<3214 then 3 else 4)) else (if x<3282 then (if x<3276 then 0 else 1) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7153 : Finset ℕ := ([250,1708,1752,1776,2680,2732,2800,3118,3162,3186,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7153 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7153 4 (fun x => (if x<2800 then (if x<1776 then (if x<1708 then 0 else (if x<1752 then 1 else 0)) else (if x<2680 then 1 else (if x<2732 then 0 else 2))) else (if x<3186 then (if x<3118 then 2 else (if x<3162 then 1 else 0)) else (if x<3214 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7154 : Finset ℕ := ([68,144,250,1594,1614,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2800,3118,3162,3180,3186,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7154 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7154 68 4
  · have he : independentCachedBranchMembers7154.erase 68=independentCachedBranchMembers7152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7152
  · have he : independentCachedBranchMembers7154.filter (independentCachedEdge 68)=independentCachedBranchMembers7153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7153
def independentCachedBranchMembers7155 : Finset ℕ := ([144,1690,1708,1752,2662,2714,2732,3118,3162,3180,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7155 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7155 4 (fun x => (if x<2732 then (if x<1752 then (if x<1690 then 0 else (if x<1708 then 0 else 1)) else (if x<2662 then 1 else (if x<2714 then 0 else 2))) else (if x<3180 then (if x<3118 then 2 else (if x<3162 then 1 else 1)) else (if x<3282 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7156 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2800,3118,3162,3180,3186,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7156 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7156 48 4
  · have he : independentCachedBranchMembers7156.erase 48=independentCachedBranchMembers7154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7154
  · have he : independentCachedBranchMembers7156.filter (independentCachedEdge 48)=independentCachedBranchMembers7155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7155
def independentCachedBranchMembers7157 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1776,2618,2638,2714,2800,3118,3162,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7157 4 (fun x => (if x<2618 then (if x<1594 then (if x<144 then (if x<68 then 0 else 0) else (if x<250 then 1 else 1)) else (if x<1690 then (if x<1614 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2638 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3162 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7158 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7158 3238 4
  · have he : independentCachedBranchMembers7158.erase 3238=independentCachedBranchMembers7156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7156
  · have he : independentCachedBranchMembers7158.filter (independentCachedEdge 3238)=independentCachedBranchMembers7157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7157
def independentCachedBranchMembers7159 : Finset ℕ := ([48,68,1594,1614,1708,1714,1734,1752,2662,2680,2714,2800,3180,3186,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7159 4 (fun x => (if x<2662 then (if x<1708 then (if x<1594 then (if x<68 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3180 then (if x<2714 then (if x<2680 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3186 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7160 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7160 2776 4
  · have he : independentCachedBranchMembers7160.erase 2776=independentCachedBranchMembers7158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7158
  · have he : independentCachedBranchMembers7160.filter (independentCachedEdge 2776)=independentCachedBranchMembers7159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7159
def independentCachedBranchMembers7161 : Finset ℕ := ([144,250,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,3118,3162,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound7161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7161 4 (fun x => (if x<2618 then (if x<1714 then (if x<1690 then (if x<250 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3118 then (if x<2662 then (if x<2638 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<3180 then (if x<3162 then 2 else 2) else (if x<3186 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7162 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1708,1714,1734,1752,1776,2618,2638,2662,2680,2714,2732,2738,2758,2776,2800,3118,3162,3180,3186,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7162 2758 4
  · have he : independentCachedBranchMembers7162.erase 2758=independentCachedBranchMembers7160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7160
  · have he : independentCachedBranchMembers7162.filter (independentCachedEdge 2758)=independentCachedBranchMembers7161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7161
def independentCachedBranchMembers7163 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7163 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7163 3244 5
  · have he : independentCachedBranchMembers7163.erase 3244=independentCachedBranchMembers7151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7151
  · have he : independentCachedBranchMembers7163.filter (independentCachedEdge 3244)=independentCachedBranchMembers7162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7162
def independentCachedBranchMembers7164 : Finset ℕ := ([68,132,238,1594,1614,1678,1702,1720,1740,1746,1764,2606,2650,2668,2674,2714,2732,2738,2758,2800,3130,3150,3174,3192,3214,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7164 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7164 5 (fun x => (if x<2674 then (if x<1720 then (if x<1594 then (if x<132 then 0 else (if x<238 then 1 else 0)) else (if x<1678 then (if x<1614 then 1 else 0) else (if x<1702 then 1 else 2))) else (if x<1764 then (if x<1740 then 2 else (if x<1746 then 2 else 2)) else (if x<2650 then (if x<2606 then 0 else 3) else (if x<2668 then 3 else 0)))) else (if x<3150 then (if x<2738 then (if x<2714 then 1 else (if x<2732 then 4 else 2)) else (if x<2800 then (if x<2758 then 2 else 0) else (if x<3130 then 4 else 3))) else (if x<3214 then (if x<3174 then 3 else (if x<3192 then 0 else 1)) else (if x<3282 then (if x<3276 then 4 else 0) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7165 : Finset ℕ := ([238,1702,1746,1764,2606,2650,2668,2714,2732,3174,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7165 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7165 4 (fun x => (if x<2668 then (if x<1764 then (if x<1702 then 0 else (if x<1746 then 0 else 1)) else (if x<2606 then 1 else (if x<2650 then 0 else 1))) else (if x<3174 then (if x<2714 then 1 else (if x<2732 then 2 else 2)) else (if x<3282 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7166 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1702,1720,1740,1746,1764,2606,2650,2668,2674,2714,2732,2738,2758,2800,3130,3150,3174,3192,3214,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7166 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7166 48 4
  · have he : independentCachedBranchMembers7166.erase 48=independentCachedBranchMembers7164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7164
  · have he : independentCachedBranchMembers7166.filter (independentCachedEdge 48)=independentCachedBranchMembers7165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7165
def independentCachedBranchMembers7167 : Finset ℕ := ([132,238,1678,1702,1720,1740,1746,1764,2606,2650,2668,2674,3130,3150,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7167 4 (fun x => (if x<2606 then (if x<1720 then (if x<1678 then (if x<238 then 0 else 0) else (if x<1702 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3130 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<3174 then (if x<3150 then 2 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
