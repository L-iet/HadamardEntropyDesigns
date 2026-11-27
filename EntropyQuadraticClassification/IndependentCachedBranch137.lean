/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch136
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7168 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1702,1720,1740,1746,1764,2606,2650,2668,2674,2714,2732,2738,2758,2800,3130,3150,3174,3192,3214,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7168 3256 4
  · have he : independentCachedBranchMembers7168.erase 3256=independentCachedBranchMembers7166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7166
  · have he : independentCachedBranchMembers7168.filter (independentCachedEdge 3256)=independentCachedBranchMembers7167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7167
def independentCachedBranchMembers7169 : Finset ℕ := ([48,68,1594,1614,1702,1720,1740,1746,2668,2674,2714,2800,3174,3192,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7169 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7169 4 (fun x => (if x<2668 then (if x<1702 then (if x<1594 then (if x<68 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1740 then (if x<1720 then 1 else 1) else (if x<1746 then 1 else 1))) else (if x<3174 then (if x<2714 then (if x<2674 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3192 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7170 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1702,1720,1740,1746,1764,2606,2650,2668,2674,2714,2732,2738,2758,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7170 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7170 3238 4
  · have he : independentCachedBranchMembers7170.erase 3238=independentCachedBranchMembers7168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7168
  · have he : independentCachedBranchMembers7170.filter (independentCachedEdge 3238)=independentCachedBranchMembers7169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7169
def independentCachedBranchMembers7171 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1764,2606,2650,2714,2800,3130,3150,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7171 4 (fun x => (if x<2606 then (if x<1594 then (if x<132 then (if x<68 then 0 else 0) else (if x<238 then 1 else 1)) else (if x<1678 then (if x<1614 then 0 else 0) else (if x<1764 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2650 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3214 then (if x<3150 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7172 : Finset ℕ := ([48,68,132,238,1594,1614,1678,1702,1720,1740,1746,1764,2606,2650,2668,2674,2714,2732,2738,2758,2776,2800,3130,3150,3174,3192,3214,3238,3256,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7172 2776 4
  · have he : independentCachedBranchMembers7172.erase 2776=independentCachedBranchMembers7170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7170
  · have he : independentCachedBranchMembers7172.filter (independentCachedEdge 2776)=independentCachedBranchMembers7171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7171
def independentCachedBranchMembers7173 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7173 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7173 2770 5
  · have he : independentCachedBranchMembers7173.erase 2770=independentCachedBranchMembers7163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7163
  · have he : independentCachedBranchMembers7173.filter (independentCachedEdge 2770)=independentCachedBranchMembers7172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7172
def independentCachedBranchMembers7174 : Finset ℕ := ([68,238,1594,1614,1650,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,2738,2758,2764,2800,3118,3162,3174,3180,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7174 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7174 5 (fun x => (if x<2662 then (if x<1702 then (if x<1614 then (if x<238 then 0 else (if x<1594 then 0 else 1)) else (if x<1650 then 0 else (if x<1690 then 2 else 2))) else (if x<1752 then (if x<1708 then 1 else (if x<1746 then 3 else 1)) else (if x<2606 then (if x<1764 then 3 else 0) else (if x<2650 then 1 else 1)))) else (if x<3162 then (if x<2758 then (if x<2668 then 0 else (if x<2738 then 4 else 1)) else (if x<2800 then (if x<2764 then 1 else 0) else (if x<3118 then 4 else 3))) else (if x<3214 then (if x<3174 then 2 else (if x<3180 then 2 else 0)) else (if x<3256 then (if x<3250 then 2 else 2) else (if x<3276 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7175 : Finset ℕ := ([238,1594,1650,1702,1708,1764,2650,2758,2764,3162,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7175 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7175 4 (fun x => (if x<2650 then (if x<1702 then (if x<1594 then 0 else (if x<1650 then 1 else 2)) else (if x<1708 then 0 else (if x<1764 then 1 else 2))) else (if x<3162 then (if x<2758 then 1 else (if x<2764 then 0 else 1)) else (if x<3214 then 2 else (if x<3276 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7176 : Finset ℕ := ([68,144,238,1594,1614,1650,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,2738,2758,2764,2800,3118,3162,3174,3180,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7176 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7176 144 4
  · have he : independentCachedBranchMembers7176.erase 144=independentCachedBranchMembers7174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7174
  · have he : independentCachedBranchMembers7176.filter (independentCachedEdge 144)=independentCachedBranchMembers7175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7175
def independentCachedBranchMembers7177 : Finset ℕ := ([68,1594,1690,1702,1752,1764,2650,2662,2758,3162,3174,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7177 4 (fun x => (if x<2650 then (if x<1702 then (if x<1594 then 0 else (if x<1690 then 0 else 1)) else (if x<1752 then 1 else (if x<1764 then 2 else 2))) else (if x<3162 then (if x<2662 then 1 else (if x<2758 then 1 else 0)) else (if x<3174 then 2 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7178 : Finset ℕ := ([12,68,144,238,1594,1614,1650,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,2738,2758,2764,2800,3118,3162,3174,3180,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7178 12 4
  · have he : independentCachedBranchMembers7178.erase 12=independentCachedBranchMembers7176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7176
  · have he : independentCachedBranchMembers7178.filter (independentCachedEdge 12)=independentCachedBranchMembers7177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7177
def independentCachedBranchMembers7179 : Finset ℕ := ([238,1594,1690,1702,1708,2650,2662,2668,2758,2764,2800,3118,3214,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7179 4 (fun x => (if x<2668 then (if x<1702 then (if x<1594 then 0 else (if x<1690 then 1 else 2)) else (if x<2650 then (if x<1708 then 0 else 1) else (if x<2662 then 1 else 0))) else (if x<3118 then (if x<2764 then (if x<2758 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3250 then (if x<3214 then 0 else 3) else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7180 : Finset ℕ := ([1702,1708,2650,2800,3118,3214] : List ℕ).toFinset
theorem independentCachedBranchBound7180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7180 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7180 3 (fun x => (if x<2800 then (if x<1708 then 0 else (if x<2650 then 1 else 0)) else (if x<3118 then 2 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7181 : Finset ℕ := ([68,238,1594,1690,1702,1708,2650,2662,2668,2758,2764,2800,3118,3214,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7181 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7181 68 3
  · have he : independentCachedBranchMembers7181.erase 68=independentCachedBranchMembers7179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7179
  · have he : independentCachedBranchMembers7181.filter (independentCachedEdge 68)=independentCachedBranchMembers7180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7180
def independentCachedBranchMembers7182 : Finset ℕ := ([12,68,144,238,1594,1614,1650,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,2738,2758,2764,2800,3118,3162,3174,3180,3214,3250,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7182 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7182 3312 4
  · have he : independentCachedBranchMembers7182.erase 3312=independentCachedBranchMembers7178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7178
  · have he : independentCachedBranchMembers7182.filter (independentCachedEdge 3312)=independentCachedBranchMembers7181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7181
def independentCachedBranchMembers7183 : Finset ℕ := ([68,144,1594,1746,1752,1764,2606,2758,2764,2800,3162,3174,3180,3214,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7183 4 (fun x => (if x<2764 then (if x<1752 then (if x<1594 then (if x<144 then 0 else 0) else (if x<1746 then 1 else 1)) else (if x<2606 then (if x<1764 then 2 else 2) else (if x<2758 then 1 else 1))) else (if x<3180 then (if x<3162 then (if x<2800 then 2 else 2) else (if x<3174 then 3 else 0)) else (if x<3250 then (if x<3214 then 3 else 3) else (if x<3256 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7184 : Finset ℕ := ([12,68,144,238,1594,1614,1650,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,2702,2738,2758,2764,2800,3118,3162,3174,3180,3214,3250,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7184 2702 4
  · have he : independentCachedBranchMembers7184.erase 2702=independentCachedBranchMembers7182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7182
  · have he : independentCachedBranchMembers7184.filter (independentCachedEdge 2702)=independentCachedBranchMembers7183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7183
def independentCachedBranchMembers7185 : Finset ℕ := ([238,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,3118,3162,3174,3180] : List ℕ).toFinset
theorem independentCachedBranchBound7185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7185 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7185 4 (fun x => (if x<2606 then (if x<1708 then (if x<1690 then 0 else (if x<1702 then 1 else 0)) else (if x<1752 then (if x<1746 then 1 else 2) else (if x<1764 then 3 else 2))) else (if x<3118 then (if x<2662 then (if x<2650 then 0 else 1) else (if x<2668 then 3 else 1)) else (if x<3174 then (if x<3162 then 3 else 2) else (if x<3180 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7186 : Finset ℕ := ([238,1702,1708,1764,2650,3162] : List ℕ).toFinset
theorem independentCachedBranchBound7186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7186 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7186 3 (fun x => (if x<1764 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<2650 then 2 else (if x<3162 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7187 : Finset ℕ := ([144,238,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,3118,3162,3174,3180] : List ℕ).toFinset
theorem independentCachedBranchBound7187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7187 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7187 144 3
  · have he : independentCachedBranchMembers7187.erase 144=independentCachedBranchMembers7185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7185
  · have he : independentCachedBranchMembers7187.filter (independentCachedEdge 144)=independentCachedBranchMembers7186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7186
def independentCachedBranchMembers7188 : Finset ℕ := ([12,48,68,144,238,1594,1614,1650,1690,1702,1708,1746,1752,1764,2606,2650,2662,2668,2702,2738,2758,2764,2800,3118,3162,3174,3180,3214,3250,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7188 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7188 48 4
  · have he : independentCachedBranchMembers7188.erase 48=independentCachedBranchMembers7184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7184
  · have he : independentCachedBranchMembers7188.filter (independentCachedEdge 48)=independentCachedBranchMembers7187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7187
def independentCachedBranchMembers7189 : Finset ℕ := ([12,18,48,68,132,144,238,250,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7189 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7189 1626 5
  · have he : independentCachedBranchMembers7189.erase 1626=independentCachedBranchMembers7173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7173
  · have he : independentCachedBranchMembers7189.filter (independentCachedEdge 1626)=independentCachedBranchMembers7188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7188
def independentCachedBranchMembers7190 : Finset ℕ := ([18,48,132,250,1594,1614,1644,1678,1702,1708,1746,1752,1776,2606,2650,2674,2680,2714,2738,2758,2764,3118,3162,3186,3192,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7190 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7190 5 (fun x => (if x<2650 then (if x<1678 then (if x<250 then (if x<48 then 0 else (if x<132 then 1 else 0)) else (if x<1614 then (if x<1594 then 1 else 0) else (if x<1644 then 2 else 3))) else (if x<1746 then (if x<1702 then 3 else (if x<1708 then 2 else 0)) else (if x<1776 then (if x<1752 then 2 else 3) else (if x<2606 then 1 else 2)))) else (if x<3118 then (if x<2714 then (if x<2674 then 0 else (if x<2680 then 1 else 3)) else (if x<2758 then (if x<2738 then 3 else 2) else (if x<2764 then 2 else 0))) else (if x<3250 then (if x<3186 then (if x<3162 then 4 else 4) else (if x<3192 then 0 else 1)) else (if x<3276 then (if x<3256 then 1 else 4) else (if x<3300 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7191 : Finset ℕ := ([132,1614,1702,1708,1776,2606,2674,2680,2714,2758,2764,3162,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7191 4 (fun x => (if x<2680 then (if x<1708 then (if x<1614 then 0 else (if x<1702 then 1 else 0)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2674 then 1 else 2))) else (if x<3162 then (if x<2758 then (if x<2714 then 0 else 3) else (if x<2764 then 3 else 1)) else (if x<3256 then (if x<3250 then 0 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7192 : Finset ℕ := ([1702,1708,2606,2714,3162,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7192 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7192 3 (fun x => (if x<2714 then (if x<1708 then 0 else (if x<2606 then 1 else 0)) else (if x<3162 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7193 : Finset ℕ := ([48,132,1614,1702,1708,1776,2606,2674,2680,2714,2758,2764,3162,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7193 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7193 48 3
  · have he : independentCachedBranchMembers7193.erase 48=independentCachedBranchMembers7191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7191
  · have he : independentCachedBranchMembers7193.filter (independentCachedEdge 48)=independentCachedBranchMembers7192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7192
def independentCachedBranchMembers7194 : Finset ℕ := ([18,48,132,250,1594,1614,1644,1678,1702,1708,1746,1752,1776,2606,2650,2674,2680,2714,2738,2758,2764,3118,3162,3186,3192,3226,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7194 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7194 3226 4
  · have he : independentCachedBranchMembers7194.erase 3226=independentCachedBranchMembers7190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7190
  · have he : independentCachedBranchMembers7194.filter (independentCachedEdge 3226)=independentCachedBranchMembers7193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7193
def independentCachedBranchMembers7195 : Finset ℕ := ([48,250,1614,1678,1746,1752,2650,2714,2758,2764,3118,3186,3192,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7195 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7195 4 (fun x => (if x<2758 then (if x<1746 then (if x<1614 then (if x<250 then 0 else 0) else (if x<1678 then 1 else 2)) else (if x<2650 then (if x<1752 then 1 else 2) else (if x<2714 then 1 else 2))) else (if x<3192 then (if x<3118 then (if x<2764 then 1 else 2) else (if x<3186 then 3 else 0)) else (if x<3256 then (if x<3250 then 3 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7196 : Finset ℕ := ([18,48,132,250,1594,1614,1644,1678,1702,1708,1746,1752,1776,2606,2650,2674,2680,2714,2738,2758,2764,2788,3118,3162,3186,3192,3226,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7196 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7196 2788 4
  · have he : independentCachedBranchMembers7196.erase 2788=independentCachedBranchMembers7194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7194
  · have he : independentCachedBranchMembers7196.filter (independentCachedEdge 2788)=independentCachedBranchMembers7195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7195
def independentCachedBranchMembers7197 : Finset ℕ := ([132,250,1678,1702,1708,1746,1752,1776,2606,2650,2674,2680,3118,3162,3186,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7197 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7197 4 (fun x => (if x<2606 then (if x<1708 then (if x<1678 then (if x<250 then 0 else 1) else (if x<1702 then 0 else 2)) else (if x<1752 then (if x<1746 then 3 else 1) else (if x<1776 then 3 else 2))) else (if x<3118 then (if x<2674 then (if x<2650 then 2 else 1) else (if x<2680 then 0 else 2)) else (if x<3186 then (if x<3162 then 3 else 3) else (if x<3192 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7198 : Finset ℕ := ([18,48,68,132,250,1594,1614,1644,1678,1702,1708,1746,1752,1776,2606,2650,2674,2680,2714,2738,2758,2764,2788,3118,3162,3186,3192,3226,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7198 68 4
  · have he : independentCachedBranchMembers7198.erase 68=independentCachedBranchMembers7196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7196
  · have he : independentCachedBranchMembers7198.filter (independentCachedEdge 68)=independentCachedBranchMembers7197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7197
def independentCachedBranchMembers7199 : Finset ℕ := ([12,18,48,68,132,144,238,250,1582,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7199 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7199 1582 5
  · have he : independentCachedBranchMembers7199.erase 1582=independentCachedBranchMembers7189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7189
  · have he : independentCachedBranchMembers7199.filter (independentCachedEdge 1582)=independentCachedBranchMembers7198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7198
end EntropyDesigns.QuadraticRefinement
