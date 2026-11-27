/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch134
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7104 : Finset ℕ := ([18,68,144,250,1614,1650,1690,1702,1708,1734,1740,1776,2618,2650,2662,2668,2738,3130,3162,3174,3180,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7104 144 4
  · have he : independentCachedBranchMembers7104.erase 144=independentCachedBranchMembers7102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7102
  · have he : independentCachedBranchMembers7104.filter (independentCachedEdge 144)=independentCachedBranchMembers7103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7103
def independentCachedBranchMembers7105 : Finset ℕ := ([12,18,48,68,144,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7105 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7105 1678 5
  · have he : independentCachedBranchMembers7105.erase 1678=independentCachedBranchMembers7099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7099
  · have he : independentCachedBranchMembers7105.filter (independentCachedEdge 1678)=independentCachedBranchMembers7104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7104
def independentCachedBranchMembers7106 : Finset ℕ := ([18,48,250,1594,1650,1714,1720,1746,1752,2618,2650,2674,2680,2714,2738,2800,3130,3162,3186,3192,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7106 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7106 5 (fun x => (if x<2674 then (if x<1714 then (if x<250 then (if x<48 then 0 else 1) else (if x<1594 then 0 else (if x<1650 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1746 then 1 else 0)) else (if x<2618 then 2 else (if x<2650 then 1 else 0)))) else (if x<3162 then (if x<2738 then (if x<2680 then 3 else (if x<2714 then 4 else 2)) else (if x<2800 then 0 else (if x<3130 then 1 else 3))) else (if x<3250 then (if x<3186 then 4 else (if x<3192 then 0 else 1)) else (if x<3256 then 1 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7107 : Finset ℕ := ([18,1650,1714,1720,1746,1752,2618,2650,2714,2800,3130,3162] : List ℕ).toFinset
theorem independentCachedBranchBound7107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7107 4 (fun x => (if x<2618 then (if x<1720 then (if x<1650 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1752 then 2 else 1))) else (if x<2800 then (if x<2650 then 0 else (if x<2714 then 3 else 1)) else (if x<3130 then 1 else (if x<3162 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7108 : Finset ℕ := ([18,48,250,1594,1650,1714,1720,1746,1752,1776,2618,2650,2674,2680,2714,2738,2800,3130,3162,3186,3192,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7108 1776 4
  · have he : independentCachedBranchMembers7108.erase 1776=independentCachedBranchMembers7106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7106
  · have he : independentCachedBranchMembers7108.filter (independentCachedEdge 1776)=independentCachedBranchMembers7107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7107
def independentCachedBranchMembers7109 : Finset ℕ := ([48,1594,1714,1720,1746,1752,2674,2680,2714,2800,3186,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7109 4 (fun x => (if x<2674 then (if x<1720 then (if x<1594 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1752 then 2 else 1))) else (if x<2800 then (if x<2680 then 0 else (if x<2714 then 3 else 1)) else (if x<3186 then 1 else (if x<3192 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7110 : Finset ℕ := ([18,48,250,1594,1650,1690,1714,1720,1746,1752,1776,2618,2650,2674,2680,2714,2738,2800,3130,3162,3186,3192,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7110 1690 4
  · have he : independentCachedBranchMembers7110.erase 1690=independentCachedBranchMembers7108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7108
  · have he : independentCachedBranchMembers7110.filter (independentCachedEdge 1690)=independentCachedBranchMembers7109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7109
def independentCachedBranchMembers7111 : Finset ℕ := ([18,48,1594,1650,2618,2650,2674,2680,3130,3162,3186,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7111 4 (fun x => (if x<2674 then (if x<1650 then (if x<48 then 0 else (if x<1594 then 1 else 0)) else (if x<2618 then 1 else (if x<2650 then 1 else 0))) else (if x<3162 then (if x<2680 then 2 else (if x<3130 then 3 else 2)) else (if x<3186 then 3 else (if x<3192 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7112 : Finset ℕ := ([18,48,144,250,1594,1650,1690,1714,1720,1746,1752,1776,2618,2650,2674,2680,2714,2738,2800,3130,3162,3186,3192,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7112 144 4
  · have he : independentCachedBranchMembers7112.erase 144=independentCachedBranchMembers7110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7110
  · have he : independentCachedBranchMembers7112.filter (independentCachedEdge 144)=independentCachedBranchMembers7111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7111
def independentCachedBranchMembers7113 : Finset ℕ := ([12,18,48,68,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7113 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7113 238 5
  · have he : independentCachedBranchMembers7113.erase 238=independentCachedBranchMembers7105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7105
  · have he : independentCachedBranchMembers7113.filter (independentCachedEdge 238)=independentCachedBranchMembers7112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7112
def independentCachedBranchMembers7114 : Finset ℕ := ([12,68,144,1614,1644,1714,1720,1746,1752,2606,2638,2662,2668,2714,2738,2800,3118,3150,3174,3180,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7114 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7114 5 (fun x => (if x<2662 then (if x<1714 then (if x<144 then (if x<68 then 0 else 1) else (if x<1614 then 0 else (if x<1644 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1746 then 1 else 0)) else (if x<2606 then 2 else (if x<2638 then 0 else 1)))) else (if x<3150 then (if x<2738 then (if x<2668 then 3 else (if x<2714 then 4 else 1)) else (if x<2800 then 0 else (if x<3118 then 2 else 3))) else (if x<3250 then (if x<3174 then 4 else (if x<3180 then 1 else 0)) else (if x<3256 then 1 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7115 : Finset ℕ := ([68,1614,1714,1720,1746,1752,2662,2668,2714,2800,3174,3180] : List ℕ).toFinset
theorem independentCachedBranchBound7115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7115 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7115 4 (fun x => (if x<2662 then (if x<1720 then (if x<1614 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1752 then 2 else 1))) else (if x<2800 then (if x<2668 then 0 else (if x<2714 then 3 else 1)) else (if x<3174 then 1 else (if x<3180 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7116 : Finset ℕ := ([12,68,144,1614,1644,1714,1720,1746,1752,1776,2606,2638,2662,2668,2714,2738,2800,3118,3150,3174,3180,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7116 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7116 1776 4
  · have he : independentCachedBranchMembers7116.erase 1776=independentCachedBranchMembers7114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7114
  · have he : independentCachedBranchMembers7116.filter (independentCachedEdge 1776)=independentCachedBranchMembers7115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7115
def independentCachedBranchMembers7117 : Finset ℕ := ([12,1644,1714,1720,1746,1752,2606,2638,2714,2800,3118,3150] : List ℕ).toFinset
theorem independentCachedBranchBound7117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7117 4 (fun x => (if x<2606 then (if x<1720 then (if x<1644 then 0 else (if x<1714 then 0 else 1)) else (if x<1746 then 2 else (if x<1752 then 2 else 1))) else (if x<2800 then (if x<2638 then 0 else (if x<2714 then 3 else 1)) else (if x<3118 then 1 else (if x<3150 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7118 : Finset ℕ := ([12,68,144,1614,1644,1690,1714,1720,1746,1752,1776,2606,2638,2662,2668,2714,2738,2800,3118,3150,3174,3180,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7118 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7118 1690 4
  · have he : independentCachedBranchMembers7118.erase 1690=independentCachedBranchMembers7116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7116
  · have he : independentCachedBranchMembers7118.filter (independentCachedEdge 1690)=independentCachedBranchMembers7117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7117
def independentCachedBranchMembers7119 : Finset ℕ := ([12,68,1614,1644,2606,2638,2662,2668,3118,3150,3174,3180] : List ℕ).toFinset
theorem independentCachedBranchBound7119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7119 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7119 4 (fun x => (if x<2662 then (if x<1644 then (if x<68 then 0 else (if x<1614 then 1 else 0)) else (if x<2606 then 1 else (if x<2638 then 0 else 1))) else (if x<3150 then (if x<2668 then 2 else (if x<3118 then 3 else 2)) else (if x<3174 then 3 else (if x<3180 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7120 : Finset ℕ := ([12,68,144,250,1614,1644,1690,1714,1720,1746,1752,1776,2606,2638,2662,2668,2714,2738,2800,3118,3150,3174,3180,3250,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7120 250 4
  · have he : independentCachedBranchMembers7120.erase 250=independentCachedBranchMembers7118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7118
  · have he : independentCachedBranchMembers7120.filter (independentCachedEdge 250)=independentCachedBranchMembers7119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7119
def independentCachedBranchMembers7121 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7121 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7121 132 5
  · have he : independentCachedBranchMembers7121.erase 132=independentCachedBranchMembers7113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7113
  · have he : independentCachedBranchMembers7121.filter (independentCachedEdge 132)=independentCachedBranchMembers7120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7120
def independentCachedBranchMembers7122 : Finset ℕ := ([18,68,132,238,1594,1644,1690,1702,1708,1734,1740,1776,2618,2650,2662,2668,2714,2732,2758,2764,2800,3118,3150,3186,3192,3214,3250,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7122 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7122 5 (fun x => (if x<2668 then (if x<1702 then (if x<238 then (if x<68 then 0 else (if x<132 then 0 else 1)) else (if x<1644 then (if x<1594 then 1 else 0) else (if x<1690 then 0 else 2))) else (if x<1776 then (if x<1734 then (if x<1708 then 1 else 2) else (if x<1740 then 2 else 1)) else (if x<2650 then (if x<2618 then 2 else 3) else (if x<2662 then 4 else 3)))) else (if x<3150 then (if x<2758 then (if x<2714 then 4 else (if x<2732 then 0 else 1)) else (if x<2800 then (if x<2764 then 1 else 0) else (if x<3118 then 3 else 3))) else (if x<3250 then (if x<3192 then (if x<3186 then 4 else 3) else (if x<3214 then 4 else 1)) else (if x<3282 then (if x<3256 then 0 else 2) else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7123 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2714,2732,2738,2758,2764,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7123 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7123 3312 5
  · have he : independentCachedBranchMembers7123.erase 3312=independentCachedBranchMembers7121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7121
  · have he : independentCachedBranchMembers7123.filter (independentCachedEdge 3312)=independentCachedBranchMembers7122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7122
def independentCachedBranchMembers7124 : Finset ℕ := ([144,250,1594,1614,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7124 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7124 5 (fun x => (if x<2638 then (if x<1702 then (if x<1594 then (if x<250 then 0 else 0) else (if x<1614 then 1 else (if x<1690 then 1 else 0))) else (if x<1746 then (if x<1720 then 1 else (if x<1740 then 2 else 2)) else (if x<1776 then 1 else (if x<2618 then 0 else 2)))) else (if x<3162 then (if x<2714 then (if x<2668 then 2 else (if x<2674 then 3 else 3)) else (if x<2800 then 4 else (if x<3118 then 4 else 1))) else (if x<3214 then (if x<3174 then 1 else (if x<3192 then 3 else 3)) else (if x<3250 then 4 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7125 : Finset ℕ := ([250,1702,1746,1776,2674,2800,3118,3162,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound7125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7125 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7125 4 (fun x => (if x<2800 then (if x<1746 then (if x<1702 then 0 else 1) else (if x<1776 then 0 else (if x<2674 then 1 else 0))) else (if x<3162 then (if x<3118 then 2 else 1) else (if x<3192 then 0 else (if x<3214 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7126 : Finset ℕ := ([68,144,250,1594,1614,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7126 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7126 68 4
  · have he : independentCachedBranchMembers7126.erase 68=independentCachedBranchMembers7124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7124
  · have he : independentCachedBranchMembers7126.filter (independentCachedEdge 68)=independentCachedBranchMembers7125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7125
def independentCachedBranchMembers7127 : Finset ℕ := ([144,1690,1702,1746,2668,2714,3118,3162,3174,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7127 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7127 4 (fun x => (if x<2714 then (if x<1702 then (if x<1690 then 0 else 0) else (if x<1746 then 1 else (if x<2668 then 1 else 0))) else (if x<3162 then (if x<3118 then 2 else 1) else (if x<3174 then 1 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7128 : Finset ℕ := ([48,68,144,250,1594,1614,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7128 48 4
  · have he : independentCachedBranchMembers7128.erase 48=independentCachedBranchMembers7126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7126
  · have he : independentCachedBranchMembers7128.filter (independentCachedEdge 48)=independentCachedBranchMembers7127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7127
def independentCachedBranchMembers7129 : Finset ℕ := ([68,144,1594,1740,1746,1776,2638,2668,2674,2714,3118,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7129 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7129 4 (fun x => (if x<2638 then (if x<1740 then (if x<144 then 0 else (if x<1594 then 0 else 1)) else (if x<1746 then 2 else (if x<1776 then 1 else 2))) else (if x<2714 then (if x<2668 then 0 else (if x<2674 then 3 else 1)) else (if x<3118 then 0 else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7130 : Finset ℕ := ([48,68,144,250,1594,1614,1650,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7130 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7130 1650 4
  · have he : independentCachedBranchMembers7130.erase 1650=independentCachedBranchMembers7128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7128
  · have he : independentCachedBranchMembers7130.filter (independentCachedEdge 1650)=independentCachedBranchMembers7129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7129
def independentCachedBranchMembers7131 : Finset ℕ := ([48,250,1614,1690,1740,1746,2618,2668,2674,2800,3162,3214] : List ℕ).toFinset
theorem independentCachedBranchBound7131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7131 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7131 4 (fun x => (if x<2618 then (if x<1690 then (if x<250 then 0 else (if x<1614 then 0 else 1)) else (if x<1740 then 1 else (if x<1746 then 2 else 2))) else (if x<2800 then (if x<2668 then 0 else (if x<2674 then 1 else 2)) else (if x<3162 then 0 else (if x<3214 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7132 : Finset ℕ := ([48,68,144,250,1594,1614,1644,1650,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7132 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7132 1644 4
  · have he : independentCachedBranchMembers7132.erase 1644=independentCachedBranchMembers7130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7130
  · have he : independentCachedBranchMembers7132.filter (independentCachedEdge 1644)=independentCachedBranchMembers7131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7131
def independentCachedBranchMembers7133 : Finset ℕ := ([48,144,1614,1702,1720,1776,2638,2800,3118,3174,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound7133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7133 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7133 4 (fun x => (if x<2638 then (if x<1702 then (if x<144 then 0 else (if x<1614 then 1 else 0)) else (if x<1720 then 2 else (if x<1776 then 1 else 2))) else (if x<3174 then (if x<2800 then 1 else (if x<3118 then 0 else 2)) else (if x<3192 then 1 else (if x<3214 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7134 : Finset ℕ := ([18,48,68,144,250,1594,1614,1644,1650,1690,1702,1720,1740,1746,1776,2618,2638,2668,2674,2714,2800,3118,3162,3174,3192,3214,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7134 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7134 18 4
  · have he : independentCachedBranchMembers7134.erase 18=independentCachedBranchMembers7132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7132
  · have he : independentCachedBranchMembers7134.filter (independentCachedEdge 18)=independentCachedBranchMembers7133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7133
def independentCachedBranchMembers7135 : Finset ℕ := ([68,250,1594,1690,1702,1720,2618,2714,3162,3174,3192,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7135 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7135 4 (fun x => (if x<2618 then (if x<1690 then (if x<250 then 0 else (if x<1594 then 1 else 0)) else (if x<1702 then 1 else (if x<1720 then 2 else 2))) else (if x<3174 then (if x<2714 then 1 else (if x<3162 then 0 else 1)) else (if x<3192 then 2 else (if x<3300 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
