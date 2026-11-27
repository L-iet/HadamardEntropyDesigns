/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch8
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1152 : Finset ℕ := ([1590,1734,1776,2620,2662,2710,2764,3102,3186,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1152 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1152 5 (fun x => (if x<3102 then (if x<2620 then (if x<1734 then 0 else (if x<1776 then 0 else 0)) else (if x<2710 then (if x<2662 then 1 else 1) else (if x<2764 then 1 else 1))) else (if x<3256 then (if x<3214 then (if x<3186 then 2 else 2) else (if x<3252 then 3 else 2)) else (if x<3288 then (if x<3284 then 3 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1153 : Finset ℕ := ([1590,1628,1642,1708,1734,1776,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1153 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1153 2668 5
  · have he : independentCachedBranchMembers1153.erase 2668=independentCachedBranchMembers1151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1151
  · have he : independentCachedBranchMembers1153.filter (independentCachedEdge 2668)=independentCachedBranchMembers1152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1152
def independentCachedBranchMembers1154 : Finset ℕ := ([1628,1708,1776,2620,2650,2730,2764,3150,3188,3214,3252,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1154 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1154 5 (fun x => (if x<3150 then (if x<2620 then (if x<1708 then 0 else (if x<1776 then 0 else 0)) else (if x<2730 then (if x<2650 then 1 else 1) else (if x<2764 then 1 else 1))) else (if x<3282 then (if x<3214 then (if x<3188 then 2 else 2) else (if x<3252 then 3 else 3)) else (if x<3298 then (if x<3288 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1155 : Finset ℕ := ([1590,1628,1642,1708,1734,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1155 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1155 2618 5
  · have he : independentCachedBranchMembers1155.erase 2618=independentCachedBranchMembers1153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1153
  · have he : independentCachedBranchMembers1155.filter (independentCachedEdge 2618)=independentCachedBranchMembers1154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1154
def independentCachedBranchMembers1156 : Finset ℕ := ([1590,1642,1734,2618,2646,2662,2668,2710,2716,2762,2800,3102,3118,3186,3192,3250,3256,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1156 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1156 5 (fun x => (if x<2762 then (if x<2646 then (if x<1734 then (if x<1642 then 0 else 0) else (if x<2618 then 0 else 0)) else (if x<2668 then (if x<2662 then 1 else 0) else (if x<2710 then 1 else (if x<2716 then 0 else 1)))) else (if x<3192 then (if x<3102 then (if x<2800 then 0 else 1) else (if x<3118 then 2 else (if x<3186 then 3 else 2))) else (if x<3256 then (if x<3250 then 3 else 3) else (if x<3284 then 2 else (if x<3300 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1157 : Finset ℕ := ([1590,1628,1642,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1157 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1157 1738 5
  · have he : independentCachedBranchMembers1157.erase 1738=independentCachedBranchMembers1155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1155
  · have he : independentCachedBranchMembers1157.filter (independentCachedEdge 1738)=independentCachedBranchMembers1156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1156
def independentCachedBranchMembers1158 : Finset ℕ := ([1628,1642,1708,2618,2646,2650,2668,2716,2730,2762,2800,3118,3150,3188,3192,3250,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1158 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1158 5 (fun x => (if x<2762 then (if x<2646 then (if x<1708 then (if x<1642 then 0 else 0) else (if x<2618 then 0 else 1)) else (if x<2668 then (if x<2650 then 1 else 0) else (if x<2716 then 0 else (if x<2730 then 0 else 0)))) else (if x<3192 then (if x<3118 then (if x<2800 then 1 else 1) else (if x<3150 then 2 else (if x<3188 then 3 else 2))) else (if x<3282 then (if x<3250 then 3 else 2) else (if x<3300 then 3 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1159 : Finset ℕ := ([1590,1628,1642,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1159 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1159 1692 5
  · have he : independentCachedBranchMembers1159.erase 1692=independentCachedBranchMembers1157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1157
  · have he : independentCachedBranchMembers1159.filter (independentCachedEdge 1692)=independentCachedBranchMembers1158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1158
def independentCachedBranchMembers1160 : Finset ℕ := ([1628,1642,1708,2618,2646,2650,2668,2716,2730,2762,2800,3102,3186,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1160 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1160 5 (fun x => (if x<2762 then (if x<2646 then (if x<1708 then (if x<1642 then 0 else 0) else (if x<2618 then 0 else 1)) else (if x<2668 then (if x<2650 then 1 else 0) else (if x<2716 then 0 else (if x<2730 then 0 else 0)))) else (if x<3252 then (if x<3102 then (if x<2800 then 1 else 1) else (if x<3186 then 2 else (if x<3214 then 2 else 3))) else (if x<3284 then (if x<3256 then 2 else 3) else (if x<3288 then 3 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1161 : Finset ℕ := ([1590,1628,1642,1644,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1161 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1161 1644 5
  · have he : independentCachedBranchMembers1161.erase 1644=independentCachedBranchMembers1159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1159
  · have he : independentCachedBranchMembers1161.filter (independentCachedEdge 1644)=independentCachedBranchMembers1160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1160
def independentCachedBranchMembers1162 : Finset ℕ := ([1590,1642,1734,2618,2646,2662,2668,2710,2716,2762,2800,3150,3188,3214,3252,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1162 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1162 5 (fun x => (if x<2762 then (if x<2646 then (if x<1734 then (if x<1642 then 0 else 0) else (if x<2618 then 0 else 0)) else (if x<2668 then (if x<2662 then 1 else 0) else (if x<2710 then 1 else (if x<2716 then 0 else 1)))) else (if x<3252 then (if x<3150 then (if x<2800 then 0 else 1) else (if x<3188 then 2 else (if x<3214 then 2 else 3))) else (if x<3288 then (if x<3282 then 3 else 2) else (if x<3298 then 3 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1163 : Finset ℕ := ([1590,1594,1628,1642,1644,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1163 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1163 1594 5
  · have he : independentCachedBranchMembers1163.erase 1594=independentCachedBranchMembers1161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1161
  · have he : independentCachedBranchMembers1163.filter (independentCachedEdge 1594)=independentCachedBranchMembers1162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1162
def independentCachedBranchMembers1164 : Finset ℕ := ([1590,1642,1644,1692,1734,2618,2620,2650,2662,2710,2730,2762,2764,2800,3118,3150,3186,3188,3256,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1164 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1164 5 (fun x => (if x<2762 then (if x<2618 then (if x<1644 then (if x<1642 then 0 else 0) else (if x<1692 then 1 else (if x<1734 then 1 else 0))) else (if x<2662 then (if x<2620 then 0 else (if x<2650 then 1 else 2)) else (if x<2710 then 0 else (if x<2730 then 0 else 2)))) else (if x<3186 then (if x<2800 then (if x<2764 then 0 else 1) else (if x<3118 then 2 else (if x<3150 then 3 else 4))) else (if x<3288 then (if x<3188 then 3 else (if x<3256 then 4 else 3)) else (if x<3298 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1165 : Finset ℕ := ([1590,1594,1628,1642,1644,1686,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1165 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1165 1686 5
  · have he : independentCachedBranchMembers1165.erase 1686=independentCachedBranchMembers1163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1163
  · have he : independentCachedBranchMembers1165.filter (independentCachedEdge 1686)=independentCachedBranchMembers1164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1164
def independentCachedBranchMembers1166 : Finset ℕ := ([1594,1628,1642,1708,1738,2620,2650,2662,2668,2710,2716,2730,2764,2800,3118,3188,3214,3250,3256,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1166 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1166 5 (fun x => (if x<2730 then (if x<2620 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1708 then 1 else (if x<1738 then 0 else 0))) else (if x<2668 then (if x<2650 then 0 else (if x<2662 then 0 else 1)) else (if x<2710 then 2 else (if x<2716 then 1 else 2)))) else (if x<3214 then (if x<2800 then (if x<2764 then 0 else 0) else (if x<3118 then 2 else (if x<3188 then 3 else 3))) else (if x<3284 then (if x<3250 then 4 else (if x<3256 then 3 else 4)) else (if x<3298 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1167 : Finset ℕ := ([1590,1594,1626,1628,1642,1644,1686,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1167 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1167 1626 5
  · have he : independentCachedBranchMembers1167.erase 1626=independentCachedBranchMembers1165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1165
  · have he : independentCachedBranchMembers1167.filter (independentCachedEdge 1626)=independentCachedBranchMembers1166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1166
def independentCachedBranchMembers1168 : Finset ℕ := ([1590,1594,1642,1644,1708,1776,2618,2620,2662,2668,2730,2800,3118,3186,3188,3192,3250,3252,3256,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1168 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1168 5 (fun x => (if x<2800 then (if x<1776 then (if x<1642 then (if x<1594 then 0 else 1) else (if x<1644 then 0 else (if x<1708 then 1 else 0))) else (if x<2662 then (if x<2618 then 0 else (if x<2620 then 2 else 1)) else (if x<2668 then 2 else (if x<2730 then 3 else 3)))) else (if x<3250 then (if x<3186 then (if x<3118 then 2 else 0) else (if x<3188 then 0 else (if x<3192 then 3 else 1))) else (if x<3298 then (if x<3252 then 3 else (if x<3256 then 0 else 2)) else (if x<3300 then 4 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1169 : Finset ℕ := ([222,1590,1594,1626,1628,1642,1644,1686,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1169 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1169 222 5
  · have he : independentCachedBranchMembers1169.erase 222=independentCachedBranchMembers1167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1167
  · have he : independentCachedBranchMembers1169.filter (independentCachedEdge 222)=independentCachedBranchMembers1168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1168
def independentCachedBranchMembers1170 : Finset ℕ := ([1590,1628,1644,1738,1776,2620,2646,2662,2668,2730,2762,2800,3102,3118,3150,3188,3250,3256,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1170 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1170 5 (fun x => (if x<2800 then (if x<2620 then (if x<1644 then (if x<1628 then 0 else 0) else (if x<1738 then 1 else (if x<1776 then 1 else 0))) else (if x<2668 then (if x<2646 then 1 else (if x<2662 then 2 else 3)) else (if x<2730 then 2 else (if x<2762 then 3 else 2)))) else (if x<3250 then (if x<3118 then (if x<3102 then 2 else 0) else (if x<3150 then 3 else (if x<3188 then 2 else 0))) else (if x<3288 then (if x<3256 then 0 else (if x<3282 then 3 else 1)) else (if x<3298 then 0 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1171 : Finset ℕ := ([132,222,1590,1594,1626,1628,1642,1644,1686,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1171 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1171 132 5
  · have he : independentCachedBranchMembers1171.erase 132=independentCachedBranchMembers1169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1169
  · have he : independentCachedBranchMembers1171.filter (independentCachedEdge 132)=independentCachedBranchMembers1170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1170
def independentCachedBranchMembers1172 : Finset ℕ := ([1594,1692,1708,1734,1776,2618,2620,2646,2662,2716,2730,2800,3102,3118,3186,3188,3214,3256,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1172 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1172 5 (fun x => (if x<2800 then (if x<2618 then (if x<1708 then (if x<1692 then 0 else 0) else (if x<1734 then 1 else (if x<1776 then 1 else 0))) else (if x<2662 then (if x<2620 then 2 else (if x<2646 then 1 else 1)) else (if x<2716 then 2 else (if x<2730 then 3 else 3)))) else (if x<3214 then (if x<3118 then (if x<3102 then 2 else 0) else (if x<3186 then 2 else (if x<3188 then 0 else 4))) else (if x<3284 then (if x<3256 then 3 else (if x<3282 then 0 else 1)) else (if x<3298 then 0 else (if x<3300 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1173 : Finset ℕ := ([72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1173 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1173 72 5
  · have he : independentCachedBranchMembers1173.erase 72=independentCachedBranchMembers1171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1171
  · have he : independentCachedBranchMembers1173.filter (independentCachedEdge 72)=independentCachedBranchMembers1172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1172
def independentCachedBranchMembers1174 : Finset ℕ := ([1628,1642,1692,1734,1738,1776,2620,2662,2716,2730,2762,2800,3118,3150,3188,3192,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1174 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1174 5 (fun x => (if x<2800 then (if x<1776 then (if x<1692 then (if x<1642 then 0 else 0) else (if x<1734 then 1 else (if x<1738 then 0 else 1))) else (if x<2716 then (if x<2620 then 0 else (if x<2662 then 1 else 2)) else (if x<2730 then 3 else (if x<2762 then 2 else 3)))) else (if x<3214 then (if x<3150 then (if x<3118 then 2 else 2) else (if x<3188 then 0 else (if x<3192 then 2 else 0))) else (if x<3284 then (if x<3252 then 3 else (if x<3256 then 1 else 2)) else (if x<3288 then 0 else (if x<3298 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1175 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1708,1734,1738,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1175 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1175 18 5
  · have he : independentCachedBranchMembers1175.erase 18=independentCachedBranchMembers1173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1173
  · have he : independentCachedBranchMembers1175.filter (independentCachedEdge 18)=independentCachedBranchMembers1174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1174
def independentCachedBranchMembers1176 : Finset ℕ := ([1590,1594,1628,1644,1692,1708,1734,1738,2620,2646,2650,2662,2710,2730,2764,2800,3102,3118,3188,3192,3252,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1176 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1176 5 (fun x => (if x<2710 then (if x<1734 then (if x<1644 then (if x<1594 then 0 else (if x<1628 then 1 else 0)) else (if x<1692 then 1 else (if x<1708 then 1 else 0))) else (if x<2646 then (if x<1738 then 0 else (if x<2620 then 1 else 0)) else (if x<2650 then 0 else (if x<2662 then 2 else 2)))) else (if x<3188 then (if x<2800 then (if x<2730 then 2 else (if x<2764 then 2 else 0)) else (if x<3102 then 2 else (if x<3118 then 3 else 4))) else (if x<3256 then (if x<3192 then 3 else (if x<3252 then 4 else 4)) else (if x<3282 then 3 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1177 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1708,1734,1738,1740,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1177 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1177 1740 5
  · have he : independentCachedBranchMembers1177.erase 1740=independentCachedBranchMembers1175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1175
  · have he : independentCachedBranchMembers1177.filter (independentCachedEdge 1740)=independentCachedBranchMembers1176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1176
def independentCachedBranchMembers1178 : Finset ℕ := ([18,222,1590,1626,1628,1686,1708,1734,2618,2620,2646,2668,2716,2762,2764,2800,3102,3150,3186,3188,3256,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1178 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1178 5 (fun x => (if x<2716 then (if x<1708 then (if x<1626 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 0 else (if x<1686 then 1 else 0))) else (if x<2620 then (if x<1734 then 1 else (if x<2618 then 1 else 2)) else (if x<2646 then 1 else (if x<2668 then 0 else 2)))) else (if x<3186 then (if x<2800 then (if x<2762 then 2 else (if x<2764 then 2 else 1)) else (if x<3102 then 2 else (if x<3150 then 0 else 3))) else (if x<3282 then (if x<3188 then 3 else (if x<3256 then 4 else 4)) else (if x<3284 then 0 else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1179 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1702,1708,1734,1738,1740,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1179 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1179 1702 5
  · have he : independentCachedBranchMembers1179.erase 1702=independentCachedBranchMembers1177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1177
  · have he : independentCachedBranchMembers1179.filter (independentCachedEdge 1702)=independentCachedBranchMembers1178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1178
def independentCachedBranchMembers1180 : Finset ℕ := ([1590,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3102,3118,3186,3188,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1180 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1180 5 (fun x => (if x<2662 then (if x<1708 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1644 then 0 else (if x<1692 then 1 else 1))) else (if x<2618 then (if x<1734 then 0 else (if x<1776 then 0 else 0)) else (if x<2620 then 2 else (if x<2646 then 1 else 2)))) else (if x<3186 then (if x<2764 then (if x<2710 then 1 else (if x<2762 then 1 else 2)) else (if x<3102 then 1 else (if x<3118 then 3 else 4))) else (if x<3252 then (if x<3188 then 3 else (if x<3250 then 4 else 4)) else (if x<3288 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1181 : Finset ℕ := ([1628,1642,1708,2620,2662,2710,2764,3118,3188,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1181 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1181 4 (fun x => (if x<2710 then (if x<1708 then (if x<1642 then 0 else 0) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<3188 then (if x<2764 then 1 else (if x<3118 then 1 else 2)) else (if x<3250 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1182 : Finset ℕ := ([1590,1626,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3102,3118,3186,3188,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1182 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1182 1626 4
  · have he : independentCachedBranchMembers1182.erase 1626=independentCachedBranchMembers1180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1180
  · have he : independentCachedBranchMembers1182.filter (independentCachedEdge 1626)=independentCachedBranchMembers1181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1181
def independentCachedBranchMembers1183 : Finset ℕ := ([1692,1708,1734,1776,2618,2620,2646,2662,3102,3118,3186,3188] : List ℕ).toFinset
theorem independentCachedBranchBound1183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1183 4 (fun x => (if x<2646 then (if x<1776 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 0 else (if x<2620 then 2 else 1))) else (if x<3118 then (if x<2662 then 1 else (if x<3102 then 2 else 3)) else (if x<3186 then 2 else (if x<3188 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1184 : Finset ℕ := ([72,1590,1626,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3102,3118,3186,3188,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1184 72 4
  · have he : independentCachedBranchMembers1184.erase 72=independentCachedBranchMembers1182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1182
  · have he : independentCachedBranchMembers1184.filter (independentCachedEdge 72)=independentCachedBranchMembers1183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1183
def independentCachedBranchMembers1185 : Finset ℕ := ([1628,1642,1692,1734,1776,2620,2662,2762,3118,3188,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1185 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1185 4 (fun x => (if x<2662 then (if x<1734 then (if x<1642 then 0 else (if x<1692 then 0 else 1)) else (if x<1776 then 0 else (if x<2620 then 0 else 1))) else (if x<3188 then (if x<2762 then 1 else (if x<3118 then 2 else 3)) else (if x<3252 then 2 else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1186 : Finset ℕ := ([18,72,1590,1626,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3102,3118,3186,3188,3250,3252,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1186 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1186 18 4
  · have he : independentCachedBranchMembers1186.erase 18=independentCachedBranchMembers1184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1184
  · have he : independentCachedBranchMembers1186.filter (independentCachedEdge 18)=independentCachedBranchMembers1185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1185
def independentCachedBranchMembers1187 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1702,1708,1734,1738,1740,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2758,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1187 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1187 2758 5
  · have he : independentCachedBranchMembers1187.erase 2758=independentCachedBranchMembers1179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1179
  · have he : independentCachedBranchMembers1187.filter (independentCachedEdge 2758)=independentCachedBranchMembers1186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1186
def independentCachedBranchMembers1188 : Finset ℕ := ([1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3102,3150,3188,3192,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1188 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1188 5 (fun x => (if x<2668 then (if x<1734 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1686 then 1 else (if x<1708 then 0 else 0))) else (if x<2620 then (if x<1738 then 1 else (if x<1776 then 0 else 0)) else (if x<2646 then 2 else (if x<2650 then 2 else 3)))) else (if x<3188 then (if x<2764 then (if x<2716 then 3 else (if x<2730 then 3 else 3)) else (if x<3102 then 2 else (if x<3150 then 4 else 1))) else (if x<3284 then (if x<3192 then 4 else (if x<3250 then 1 else 4)) else (if x<3288 then 1 else (if x<3298 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1189 : Finset ℕ := ([1594,1686,1738,2650,2668,2716,2730,3150,3192,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1189 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1189 4 (fun x => (if x<2716 then (if x<1738 then (if x<1686 then 0 else 0) else (if x<2650 then 0 else (if x<2668 then 1 else 1))) else (if x<3192 then (if x<2730 then 1 else (if x<3150 then 1 else 2)) else (if x<3284 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1190 : Finset ℕ := ([1590,1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3102,3150,3188,3192,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1190 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1190 1590 4
  · have he : independentCachedBranchMembers1190.erase 1590=independentCachedBranchMembers1188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1188
  · have he : independentCachedBranchMembers1190.filter (independentCachedEdge 1590)=independentCachedBranchMembers1189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1189
def independentCachedBranchMembers1191 : Finset ℕ := ([1590,1594,1642,1708,1776,2620,2668,2730,3188,3192,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1191 4 (fun x => (if x<2668 then (if x<1708 then (if x<1594 then 0 else (if x<1642 then 1 else 0)) else (if x<1776 then 0 else (if x<2620 then 0 else 1))) else (if x<3192 then (if x<2730 then 2 else (if x<3188 then 1 else 2)) else (if x<3250 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1192 : Finset ℕ := ([222,1590,1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3102,3150,3188,3192,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1192 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1192 222 4
  · have he : independentCachedBranchMembers1192.erase 222=independentCachedBranchMembers1190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1190
  · have he : independentCachedBranchMembers1192.filter (independentCachedEdge 222)=independentCachedBranchMembers1191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1191
def independentCachedBranchMembers1193 : Finset ℕ := ([1594,1708,1734,1776,2620,2646,2716,2730,3102,3188,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1193 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1193 4 (fun x => (if x<2716 then (if x<1776 then (if x<1708 then 0 else (if x<1734 then 0 else 1)) else (if x<2620 then 0 else (if x<2646 then 1 else 1))) else (if x<3188 then (if x<2730 then 2 else (if x<3102 then 2 else 3)) else (if x<3284 then 3 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1194 : Finset ℕ := ([72,222,1590,1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3102,3150,3188,3192,3250,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1194 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1194 72 4
  · have he : independentCachedBranchMembers1194.erase 72=independentCachedBranchMembers1192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1192
  · have he : independentCachedBranchMembers1194.filter (independentCachedEdge 72)=independentCachedBranchMembers1193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1193
def independentCachedBranchMembers1195 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1702,1708,1734,1738,1740,1776,2618,2620,2646,2650,2662,2668,2710,2716,2730,2732,2758,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1195 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1195 2732 5
  · have he : independentCachedBranchMembers1195.erase 2732=independentCachedBranchMembers1187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1187
  · have he : independentCachedBranchMembers1195.filter (independentCachedEdge 2732)=independentCachedBranchMembers1194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1194
def independentCachedBranchMembers1196 : Finset ℕ := ([1590,1628,1642,1708,1734,1776,2618,2650,2662,2668,2710,2716,2730,2762,3118,3150,3186,3192,3252,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1196 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1196 5 (fun x => (if x<2716 then (if x<1776 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1708 then 0 else (if x<1734 then 0 else 0))) else (if x<2662 then (if x<2618 then 0 else (if x<2650 then 1 else 2)) else (if x<2668 then 1 else (if x<2710 then 2 else 1)))) else (if x<3186 then (if x<2762 then (if x<2730 then 2 else 2) else (if x<3118 then 1 else (if x<3150 then 3 else 4))) else (if x<3284 then (if x<3192 then 3 else (if x<3252 then 4 else 3)) else (if x<3298 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1197 : Finset ℕ := ([1590,1628,1776,2662,2668,2730,2762,3118,3150,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1197 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1197 4 (fun x => (if x<2730 then (if x<1776 then (if x<1628 then 0 else 0) else (if x<2662 then 0 else (if x<2668 then 1 else 2))) else (if x<3150 then (if x<2762 then 1 else (if x<3118 then 2 else 1)) else (if x<3298 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1198 : Finset ℕ := ([132,1590,1628,1642,1708,1734,1776,2618,2650,2662,2668,2710,2716,2730,2762,3118,3150,3186,3192,3252,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1198 132 4
  · have he : independentCachedBranchMembers1198.erase 132=independentCachedBranchMembers1196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1196
  · have he : independentCachedBranchMembers1198.filter (independentCachedEdge 132)=independentCachedBranchMembers1197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1197
def independentCachedBranchMembers1199 : Finset ℕ := ([1708,1734,1776,2618,2662,2716,2730,3118,3186,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1199 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1199 4 (fun x => (if x<2716 then (if x<1776 then (if x<1734 then 0 else 0) else (if x<2618 then 0 else (if x<2662 then 1 else 1))) else (if x<3186 then (if x<2730 then 2 else (if x<3118 then 2 else 1)) else (if x<3284 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1200 : Finset ℕ := ([72,132,1590,1628,1642,1708,1734,1776,2618,2650,2662,2668,2710,2716,2730,2762,3118,3150,3186,3192,3252,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1200 72 4
  · have he : independentCachedBranchMembers1200.erase 72=independentCachedBranchMembers1198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1198
  · have he : independentCachedBranchMembers1200.filter (independentCachedEdge 72)=independentCachedBranchMembers1199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1199
def independentCachedBranchMembers1201 : Finset ℕ := ([1590,1628,1708,1734,2650,2662,2710,2730,3118,3192,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1201 4 (fun x => (if x<2710 then (if x<1734 then (if x<1628 then 0 else (if x<1708 then 0 else 0)) else (if x<2650 then 0 else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<2730 then 1 else (if x<3118 then 1 else 2)) else (if x<3252 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1202 : Finset ℕ := ([72,132,1590,1628,1642,1708,1734,1740,1776,2618,2650,2662,2668,2710,2716,2730,2762,3118,3150,3186,3192,3252,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1202 1740 4
  · have he : independentCachedBranchMembers1202.erase 1740=independentCachedBranchMembers1200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1200
  · have he : independentCachedBranchMembers1202.filter (independentCachedEdge 1740)=independentCachedBranchMembers1201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1201
def independentCachedBranchMembers1203 : Finset ℕ := ([1590,1628,1708,1734,2618,2668,2716,2762,3150,3186,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1203 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1203 4 (fun x => (if x<2716 then (if x<1734 then (if x<1628 then 0 else (if x<1708 then 0 else 0)) else (if x<2618 then 0 else (if x<2668 then 1 else 1))) else (if x<3186 then (if x<2762 then 1 else (if x<3150 then 1 else 2)) else (if x<3284 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1204 : Finset ℕ := ([72,132,1590,1628,1642,1702,1708,1734,1740,1776,2618,2650,2662,2668,2710,2716,2730,2762,3118,3150,3186,3192,3252,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1204 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1204 1702 4
  · have he : independentCachedBranchMembers1204.erase 1702=independentCachedBranchMembers1202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1202
  · have he : independentCachedBranchMembers1204.filter (independentCachedEdge 1702)=independentCachedBranchMembers1203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1203
def independentCachedBranchMembers1205 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1702,1708,1734,1738,1740,1776,2618,2620,2646,2650,2662,2668,2710,2714,2716,2730,2732,2758,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1205 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1205 2714 5
  · have he : independentCachedBranchMembers1205.erase 2714=independentCachedBranchMembers1195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1195
  · have he : independentCachedBranchMembers1205.filter (independentCachedEdge 2714)=independentCachedBranchMembers1204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1204
def independentCachedBranchMembers1206 : Finset ℕ := ([1594,1628,1642,1686,1708,1738,1776,2620,2646,2650,2668,2716,2730,2764,3118,3186,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1206 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1206 5 (fun x => (if x<2716 then (if x<1738 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1686 then 1 else (if x<1708 then 0 else 0))) else (if x<2646 then (if x<1776 then 0 else (if x<2620 then 0 else 2)) else (if x<2650 then 2 else (if x<2668 then 1 else 1)))) else (if x<3214 then (if x<2764 then (if x<2730 then 1 else 1) else (if x<3118 then 2 else (if x<3186 then 3 else 3))) else (if x<3282 then (if x<3252 then 4 else (if x<3256 then 3 else 4)) else (if x<3300 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1207 : Finset ℕ := ([1594,1686,1738,2650,2668,2716,2730,3118,3186,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1207 4 (fun x => (if x<2716 then (if x<1738 then (if x<1686 then 0 else 0) else (if x<2650 then 0 else (if x<2668 then 1 else 1))) else (if x<3186 then (if x<2730 then 1 else (if x<3118 then 1 else 2)) else (if x<3252 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1208 : Finset ℕ := ([1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3118,3186,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1208 1734 4
  · have he : independentCachedBranchMembers1208.erase 1734=independentCachedBranchMembers1206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1206
  · have he : independentCachedBranchMembers1208.filter (independentCachedEdge 1734)=independentCachedBranchMembers1207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1207
def independentCachedBranchMembers1209 : Finset ℕ := ([1594,1686,1738,2650,2668,2716,2730,3214,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1209 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1209 4 (fun x => (if x<2716 then (if x<1738 then (if x<1686 then 0 else 0) else (if x<2650 then 0 else (if x<2668 then 1 else 1))) else (if x<3256 then (if x<2730 then 1 else (if x<3214 then 1 else 2)) else (if x<3282 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1210 : Finset ℕ := ([1590,1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3118,3186,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1210 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1210 1590 4
  · have he : independentCachedBranchMembers1210.erase 1590=independentCachedBranchMembers1208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1208
  · have he : independentCachedBranchMembers1210.filter (independentCachedEdge 1590)=independentCachedBranchMembers1209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1209
def independentCachedBranchMembers1211 : Finset ℕ := ([1590,1628,1738,1776,2620,2646,2668,2730,3118,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1211 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1211 4 (fun x => (if x<2668 then (if x<1776 then (if x<1628 then 0 else (if x<1738 then 0 else 1)) else (if x<2620 then 0 else (if x<2646 then 1 else 2))) else (if x<3256 then (if x<2730 then 2 else (if x<3118 then 1 else 3)) else (if x<3282 then 3 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1212 : Finset ℕ := ([132,1590,1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3118,3186,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1212 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1212 132 4
  · have he : independentCachedBranchMembers1212.erase 132=independentCachedBranchMembers1210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1210
  · have he : independentCachedBranchMembers1212.filter (independentCachedEdge 132)=independentCachedBranchMembers1211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1211
def independentCachedBranchMembers1213 : Finset ℕ := ([1628,1642,1734,1738,1776,2620,2716,2730,3118,3214,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1213 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1213 4 (fun x => (if x<2716 then (if x<1738 then (if x<1642 then 0 else (if x<1734 then 0 else 0)) else (if x<1776 then 1 else (if x<2620 then 0 else 1))) else (if x<3214 then (if x<2730 then 2 else (if x<3118 then 1 else 3)) else (if x<3252 then 2 else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1214 : Finset ℕ := ([18,132,1590,1594,1628,1642,1686,1708,1734,1738,1776,2620,2646,2650,2668,2716,2730,2764,3118,3186,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1214 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1214 18 4
  · have he : independentCachedBranchMembers1214.erase 18=independentCachedBranchMembers1212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1212
  · have he : independentCachedBranchMembers1214.filter (independentCachedEdge 18)=independentCachedBranchMembers1213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1213
def independentCachedBranchMembers1215 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1702,1708,1734,1738,1740,1776,2618,2620,2646,2650,2652,2662,2668,2710,2714,2716,2730,2732,2758,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1215 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1215 2652 5
  · have he : independentCachedBranchMembers1215.erase 2652=independentCachedBranchMembers1205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1205
  · have he : independentCachedBranchMembers1215.filter (independentCachedEdge 2652)=independentCachedBranchMembers1214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1214
def independentCachedBranchMembers1216 : Finset ℕ := ([1590,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3150,3192,3214,3256,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1216 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1216 5 (fun x => (if x<2662 then (if x<1708 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1644 then 0 else (if x<1692 then 1 else 1))) else (if x<2618 then (if x<1734 then 0 else (if x<1776 then 0 else 0)) else (if x<2620 then 2 else (if x<2646 then 1 else 2)))) else (if x<3214 then (if x<2764 then (if x<2710 then 1 else (if x<2762 then 1 else 2)) else (if x<3150 then 1 else (if x<3192 then 3 else 3))) else (if x<3284 then (if x<3256 then 4 else (if x<3282 then 4 else 3)) else (if x<3298 then 4 else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1217 : Finset ℕ := ([1628,1642,1708,2620,2662,2710,2764,3214,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1217 4 (fun x => (if x<2710 then (if x<1708 then (if x<1642 then 0 else 0) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<3256 then (if x<2764 then 1 else (if x<3214 then 1 else 2)) else (if x<3284 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1218 : Finset ℕ := ([1590,1626,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3150,3192,3214,3256,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1218 1626 4
  · have he : independentCachedBranchMembers1218.erase 1626=independentCachedBranchMembers1216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1216
  · have he : independentCachedBranchMembers1218.filter (independentCachedEdge 1626)=independentCachedBranchMembers1217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1217
def independentCachedBranchMembers1219 : Finset ℕ := ([1590,1642,1644,1708,1776,2618,2620,2662,3192,3256,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1219 4 (fun x => (if x<2620 then (if x<1708 then (if x<1642 then 0 else (if x<1644 then 0 else 1)) else (if x<1776 then 0 else (if x<2618 then 0 else 2))) else (if x<3256 then (if x<2662 then 1 else (if x<3192 then 1 else 2)) else (if x<3298 then 3 else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1220 : Finset ℕ := ([222,1590,1626,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3150,3192,3214,3256,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1220 222 4
  · have he : independentCachedBranchMembers1220.erase 222=independentCachedBranchMembers1218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1218
  · have he : independentCachedBranchMembers1220.filter (independentCachedEdge 222)=independentCachedBranchMembers1219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1219
def independentCachedBranchMembers1221 : Finset ℕ := ([1590,1628,1644,1776,2620,2646,2662,2762,3150,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1221 4 (fun x => (if x<2662 then (if x<1776 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<2620 then 0 else (if x<2646 then 1 else 2))) else (if x<3256 then (if x<2762 then 1 else (if x<3150 then 2 else 2)) else (if x<3282 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1222 : Finset ℕ := ([132,222,1590,1626,1628,1642,1644,1692,1708,1734,1776,2618,2620,2646,2662,2710,2762,2764,3150,3192,3214,3256,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1222 132 4
  · have he : independentCachedBranchMembers1222.erase 132=independentCachedBranchMembers1220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1220
  · have he : independentCachedBranchMembers1222.filter (independentCachedEdge 132)=independentCachedBranchMembers1221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1221
def independentCachedBranchMembers1223 : Finset ℕ := ([18,72,132,222,1590,1594,1626,1628,1642,1644,1686,1692,1702,1708,1734,1738,1740,1776,2614,2618,2620,2646,2650,2652,2662,2668,2710,2714,2716,2730,2732,2758,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1223 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1223 2614 5
  · have he : independentCachedBranchMembers1223.erase 2614=independentCachedBranchMembers1215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1215
  · have he : independentCachedBranchMembers1223.filter (independentCachedEdge 2614)=independentCachedBranchMembers1222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1222
def independentCachedBranchMembers1224 : Finset ℕ := ([222,1590,1594,1628,1644,1692,1708,1734,1738,2620,2646,2650,2662,2710,2714,2730,2764,2800,3150,3186,3214,3250,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1224 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1224 5 (fun x => (if x<2710 then (if x<1708 then (if x<1628 then (if x<1590 then 0 else (if x<1594 then 1 else 2)) else (if x<1644 then 0 else (if x<1692 then 1 else 1))) else (if x<2620 then (if x<1734 then 2 else (if x<1738 then 0 else 2)) else (if x<2650 then (if x<2646 then 1 else 0) else (if x<2662 then 2 else 1)))) else (if x<3186 then (if x<2764 then (if x<2714 then 1 else (if x<2730 then 3 else 2)) else (if x<2800 then 0 else (if x<3150 then 3 else 0))) else (if x<3284 then (if x<3214 then 4 else (if x<3250 then 3 else 3)) else (if x<3300 then (if x<3288 then 0 else 3) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1225 : Finset ℕ := ([1628,1692,1734,1738,2620,2662,2730,2800,3150,3214,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1225 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1225 4 (fun x => (if x<2730 then (if x<1738 then (if x<1692 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then 1 else (if x<2662 then 0 else 2))) else (if x<3214 then (if x<2800 then 2 else (if x<3150 then 2 else 3)) else (if x<3284 then 1 else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1226 : Finset ℕ := ([18,222,1590,1594,1628,1644,1692,1708,1734,1738,2620,2646,2650,2662,2710,2714,2730,2764,2800,3150,3186,3214,3250,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1226 18 4
  · have he : independentCachedBranchMembers1226.erase 18=independentCachedBranchMembers1224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1224
  · have he : independentCachedBranchMembers1226.filter (independentCachedEdge 18)=independentCachedBranchMembers1225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1225
def independentCachedBranchMembers1227 : Finset ℕ := ([1590,1628,1644,1738,2620,2662,2730,2800,3150,3250,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1227 4 (fun x => (if x<2730 then (if x<1738 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<2620 then 1 else (if x<2662 then 0 else 2))) else (if x<3250 then (if x<2800 then 2 else (if x<3150 then 2 else 1)) else (if x<3288 then 3 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1228 : Finset ℕ := ([1590,1628,2662,2730,3150,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1228 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1228 3 (fun x => (if x<2730 then (if x<1628 then 0 else (if x<2662 then 0 else 1)) else (if x<3150 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1229 : Finset ℕ := ([1590,1628,1644,1738,2620,2662,2714,2730,2800,3150,3250,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1229 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1229 2714 3
  · have he : independentCachedBranchMembers1229.erase 2714=independentCachedBranchMembers1227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1227
  · have he : independentCachedBranchMembers1229.filter (independentCachedEdge 2714)=independentCachedBranchMembers1228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1228
def independentCachedBranchMembers1230 : Finset ℕ := ([1644,1738,2662,2730,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1230 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1230 3 (fun x => (if x<2730 then (if x<1738 then 0 else (if x<2662 then 0 else 1)) else (if x<3250 then 1 else (if x<3288 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1231 : Finset ℕ := ([1590,1628,1644,1738,2620,2646,2662,2714,2730,2800,3150,3250,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1231 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1231 2646 3
  · have he : independentCachedBranchMembers1231.erase 2646=independentCachedBranchMembers1229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1229
  · have he : independentCachedBranchMembers1231.filter (independentCachedEdge 2646)=independentCachedBranchMembers1230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1230
def independentCachedBranchMembers1232 : Finset ℕ := ([18,132,222,1590,1594,1628,1644,1692,1708,1734,1738,2620,2646,2650,2662,2710,2714,2730,2764,2800,3150,3186,3214,3250,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1232 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1232 132 4
  · have he : independentCachedBranchMembers1232.erase 132=independentCachedBranchMembers1226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1226
  · have he : independentCachedBranchMembers1232.filter (independentCachedEdge 132)=independentCachedBranchMembers1231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1231
def independentCachedBranchMembers1233 : Finset ℕ := ([1594,1692,1708,1734,2620,2662,2714,2730,2800,3186,3214,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1233 4 (fun x => (if x<2714 then (if x<1734 then (if x<1692 then 0 else (if x<1708 then 0 else 1)) else (if x<2620 then 1 else (if x<2662 then 0 else 2))) else (if x<3186 then (if x<2730 then 0 else (if x<2800 then 2 else 2)) else (if x<3284 then (if x<3214 then 3 else 1) else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1234 : Finset ℕ := ([1594,1692,2662,2730,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1234 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1234 3 (fun x => (if x<2730 then (if x<1692 then 0 else (if x<2662 then 0 else 1)) else (if x<3214 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1235 : Finset ℕ := ([1594,1692,1708,1734,2620,2646,2662,2714,2730,2800,3186,3214,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1235 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1235 2646 3
  · have he : independentCachedBranchMembers1235.erase 2646=independentCachedBranchMembers1233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1233
  · have he : independentCachedBranchMembers1235.filter (independentCachedEdge 2646)=independentCachedBranchMembers1234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1234
def independentCachedBranchMembers1236 : Finset ℕ := ([18,72,132,222,1590,1594,1628,1644,1692,1708,1734,1738,2620,2646,2650,2662,2710,2714,2730,2764,2800,3150,3186,3214,3250,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1236 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1236 72 4
  · have he : independentCachedBranchMembers1236.erase 72=independentCachedBranchMembers1232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1232
  · have he : independentCachedBranchMembers1236.filter (independentCachedEdge 72)=independentCachedBranchMembers1235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1235
def independentCachedBranchMembers1237 : Finset ℕ := ([18,72,132,222,1590,1594,1596,1626,1628,1642,1644,1686,1692,1702,1708,1734,1738,1740,1776,2614,2618,2620,2646,2650,2652,2662,2668,2710,2714,2716,2730,2732,2758,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1237 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1237 1596 5
  · have he : independentCachedBranchMembers1237.erase 1596=independentCachedBranchMembers1223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1223
  · have he : independentCachedBranchMembers1237.filter (independentCachedEdge 1596)=independentCachedBranchMembers1236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1236
def independentCachedBranchMembers1238 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1238 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1238 3312 6
  · have he : independentCachedBranchMembers1238.erase 3312=independentCachedBranchMembers1144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1144
  · have he : independentCachedBranchMembers1238.filter (independentCachedEdge 3312)=independentCachedBranchMembers1237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1237
def independentCachedBranchMembers1239 : Finset ℕ := ([12,48,192,252,1596,1686,1720,1740,1776,2618,2620,2638,2710,2732,2776,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1239 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1239 6 (fun x => (if x<2776 then (if x<1740 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1686 then (if x<1596 then 0 else 0) else (if x<1720 then 1 else 1))) else (if x<2620 then (if x<1776 then 0 else (if x<2618 then 0 else 2)) else (if x<2710 then (if x<2638 then 3 else 2) else (if x<2732 then 2 else 2)))) else (if x<3228 then (if x<3126 then (if x<2800 then 2 else (if x<3102 then 3 else 3)) else (if x<3192 then (if x<3180 then 4 else 4) else (if x<3214 then 1 else 4))) else (if x<3270 then (if x<3250 then 1 else (if x<3252 then 1 else 3)) else (if x<3284 then (if x<3282 then 5 else 3) else (if x<3304 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1240 : Finset ℕ := ([1596,1686,1720,1740,1776,2618,2638,2732,2776,3102,3192,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1240 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1240 5 (fun x => (if x<2638 then (if x<1740 then (if x<1686 then 0 else (if x<1720 then 0 else 1)) else (if x<1776 then 0 else (if x<2618 then 0 else 1))) else (if x<3102 then (if x<2732 then 1 else (if x<2776 then 1 else 1)) else (if x<3252 then (if x<3192 then 2 else 2) else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1241 : Finset ℕ := ([12,48,192,252,1596,1686,1720,1740,1776,2618,2620,2638,2710,2732,2764,2776,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1241 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1241 2764 5
  · have he : independentCachedBranchMembers1241.erase 2764=independentCachedBranchMembers1239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1239
  · have he : independentCachedBranchMembers1241.filter (independentCachedEdge 2764)=independentCachedBranchMembers1240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1240
def independentCachedBranchMembers1242 : Finset ℕ := ([12,48,1740,1776,2620,2638,2710,2776,3126,3192,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1242 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1242 5 (fun x => (if x<2776 then (if x<1776 then (if x<48 then 0 else (if x<1740 then 0 else 0)) else (if x<2638 then (if x<2620 then 0 else 1) else (if x<2710 then 0 else 1))) else (if x<3214 then (if x<3126 then 1 else (if x<3192 then 1 else 1)) else (if x<3250 then (if x<3228 then 0 else 1) else (if x<3282 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1243 : Finset ℕ := ([12,48,192,252,1596,1686,1720,1740,1764,1776,2618,2620,2638,2710,2732,2764,2776,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1243 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1243 1764 5
  · have he : independentCachedBranchMembers1243.erase 1764=independentCachedBranchMembers1241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1241
  · have he : independentCachedBranchMembers1243.filter (independentCachedEdge 1764)=independentCachedBranchMembers1242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1242
def independentCachedBranchMembers1244 : Finset ℕ := ([12,252,1596,1740,2618,2710,2732,2800,3102,3180,3192,3228,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1244 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1244 5 (fun x => (if x<2800 then (if x<1740 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<2710 then (if x<2618 then 0 else 1) else (if x<2732 then 1 else 0))) else (if x<3192 then (if x<3102 then 1 else (if x<3180 then 1 else 0)) else (if x<3250 then (if x<3228 then 1 else 0) else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1245 : Finset ℕ := ([12,48,192,252,1596,1686,1720,1738,1740,1764,1776,2618,2620,2638,2710,2732,2764,2776,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1245 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1245 1738 5
  · have he : independentCachedBranchMembers1245.erase 1738=independentCachedBranchMembers1243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1243
  · have he : independentCachedBranchMembers1245.filter (independentCachedEdge 1738)=independentCachedBranchMembers1244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1244
def independentCachedBranchMembers1246 : Finset ℕ := ([192,252,1740,1776,2620,2638,2710,2776,3102,3180,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1246 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1246 5 (fun x => (if x<2776 then (if x<1776 then (if x<252 then 0 else (if x<1740 then 0 else 0)) else (if x<2638 then (if x<2620 then 0 else 1) else (if x<2710 then 1 else 1))) else (if x<3252 then (if x<3102 then 0 else (if x<3180 then 1 else 1)) else (if x<3284 then (if x<3270 then 1 else 1) else (if x<3304 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1247 : Finset ℕ := ([12,48,192,252,1596,1650,1686,1720,1738,1740,1764,1776,2618,2620,2638,2710,2732,2764,2776,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1247 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1247 1650 5
  · have he : independentCachedBranchMembers1247.erase 1650=independentCachedBranchMembers1245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1245
  · have he : independentCachedBranchMembers1247.filter (independentCachedEdge 1650)=independentCachedBranchMembers1246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1246
def independentCachedBranchMembers1248 : Finset ℕ := ([48,192,1596,1740,2618,2710,2732,2800,3126,3214,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1248 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1248 5 (fun x => (if x<2800 then (if x<1740 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<2710 then (if x<2618 then 0 else 0) else (if x<2732 then 1 else 1))) else (if x<3252 then (if x<3126 then 1 else (if x<3214 then 0 else 1)) else (if x<3282 then (if x<3270 then 1 else 0) else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1249 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1686,1720,1738,1740,1764,1776,2618,2620,2638,2710,2732,2764,2776,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1249 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1249 1628 5
  · have he : independentCachedBranchMembers1249.erase 1628=independentCachedBranchMembers1247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1247
  · have he : independentCachedBranchMembers1249.filter (independentCachedEdge 1628)=independentCachedBranchMembers1248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1248
def independentCachedBranchMembers1250 : Finset ℕ := ([12,48,1596,1650,1686,1720,2618,2732,2764,2800,3126,3192,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1250 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1250 5 (fun x => (if x<2764 then (if x<1686 then (if x<1596 then (if x<48 then 0 else 0) else (if x<1650 then 0 else 0)) else (if x<2618 then (if x<1720 then 1 else 1) else (if x<2732 then 2 else 2))) else (if x<3214 then (if x<3126 then (if x<2800 then 3 else 2) else (if x<3192 then 3 else 1)) else (if x<3250 then (if x<3228 then 3 else 1) else (if x<3282 then 1 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1251 : Finset ℕ := ([12,48,3126,3192,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1251 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1251 4 (fun x => (if x<3214 then (if x<3126 then (if x<48 then 0 else 0) else (if x<3192 then 1 else 1)) else (if x<3250 then (if x<3228 then 0 else 1) else (if x<3282 then 0 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1252 : Finset ℕ := ([12,48,1596,1650,1686,1720,1764,2618,2732,2764,2800,3126,3192,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1252 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1252 1764 4
  · have he : independentCachedBranchMembers1252.erase 1764=independentCachedBranchMembers1250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1250
  · have he : independentCachedBranchMembers1252.filter (independentCachedEdge 1764)=independentCachedBranchMembers1251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1251
def independentCachedBranchMembers1253 : Finset ℕ := ([12,1596,2618,2732,2800,3192,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1253 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1253 4 (fun x => (if x<2800 then (if x<2618 then (if x<1596 then 0 else 0) else (if x<2732 then 1 else 0)) else (if x<3228 then (if x<3192 then 1 else 1) else (if x<3250 then 0 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1254 : Finset ℕ := ([12,48,1596,1650,1686,1720,1738,1764,2618,2732,2764,2800,3126,3192,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1254 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1254 1738 4
  · have he : independentCachedBranchMembers1254.erase 1738=independentCachedBranchMembers1252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1252
  · have he : independentCachedBranchMembers1254.filter (independentCachedEdge 1738)=independentCachedBranchMembers1253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1253
def independentCachedBranchMembers1255 : Finset ℕ := ([48,1596,2618,2732,2800,3126,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1255 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1255 4 (fun x => (if x<2800 then (if x<2618 then (if x<1596 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<3214 then (if x<3126 then 1 else 0) else (if x<3282 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1256 : Finset ℕ := ([12,48,1596,1628,1650,1686,1720,1738,1764,2618,2732,2764,2800,3126,3192,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1256 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1256 1628 4
  · have he : independentCachedBranchMembers1256.erase 1628=independentCachedBranchMembers1254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1254
  · have he : independentCachedBranchMembers1256.filter (independentCachedEdge 1628)=independentCachedBranchMembers1255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1255
def independentCachedBranchMembers1257 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1686,1720,1738,1740,1764,1776,2618,2620,2638,2710,2732,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1257 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1257 2788 5
  · have he : independentCachedBranchMembers1257.erase 2788=independentCachedBranchMembers1249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1249
  · have he : independentCachedBranchMembers1257.filter (independentCachedEdge 2788)=independentCachedBranchMembers1256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1256
def independentCachedBranchMembers1258 : Finset ℕ := ([12,252,1628,1650,1686,1720,1738,1764,1776,2620,2638,2764,2776,3102,3180,3192,3228,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1258 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1258 5 (fun x => (if x<2620 then (if x<1686 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1650 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 1) else (if x<1764 then 1 else (if x<1776 then 1 else 0)))) else (if x<3180 then (if x<2764 then (if x<2638 then 2 else 2) else (if x<2776 then 3 else (if x<3102 then 2 else 4))) else (if x<3228 then (if x<3192 then 3 else 4) else (if x<3250 then 3 else (if x<3284 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1259 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1686,1720,1738,1740,1764,1776,2618,2620,2638,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1259 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1259 2762 5
  · have he : independentCachedBranchMembers1259.erase 2762=independentCachedBranchMembers1257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1257
  · have he : independentCachedBranchMembers1259.filter (independentCachedEdge 2762)=independentCachedBranchMembers1258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1258
def independentCachedBranchMembers1260 : Finset ℕ := ([192,252,1596,1686,1720,1738,1764,2618,2732,2764,2800,3102,3180,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1260 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1260 5 (fun x => (if x<2732 then (if x<1720 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1686 then 0 else 1)) else (if x<1764 then (if x<1738 then 1 else 1) else (if x<2618 then 0 else 2))) else (if x<3180 then (if x<2800 then (if x<2764 then 2 else 3) else (if x<3102 then 2 else 4)) else (if x<3270 then (if x<3252 then 3 else 1) else (if x<3284 then 1 else (if x<3304 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1261 : Finset ℕ := ([192,252,3102,3180,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1261 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1261 4 (fun x => (if x<3252 then (if x<3102 then (if x<252 then 0 else 0) else (if x<3180 then 1 else 1)) else (if x<3284 then (if x<3270 then 1 else 1) else (if x<3304 then 0 else 0))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1262 : Finset ℕ := ([192,252,1596,1650,1686,1720,1738,1764,2618,2732,2764,2800,3102,3180,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1262 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1262 1650 4
  · have he : independentCachedBranchMembers1262.erase 1650=independentCachedBranchMembers1260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1260
  · have he : independentCachedBranchMembers1262.filter (independentCachedEdge 1650)=independentCachedBranchMembers1261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1261
def independentCachedBranchMembers1263 : Finset ℕ := ([192,1596,2618,2732,2800,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1263 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1263 4 (fun x => (if x<2800 then (if x<2618 then (if x<1596 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<3270 then (if x<3252 then 1 else 1) else (if x<3304 then 0 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1264 : Finset ℕ := ([192,252,1596,1628,1650,1686,1720,1738,1764,2618,2732,2764,2800,3102,3180,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1264 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1264 1628 4
  · have he : independentCachedBranchMembers1264.erase 1628=independentCachedBranchMembers1262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1262
  · have he : independentCachedBranchMembers1264.filter (independentCachedEdge 1628)=independentCachedBranchMembers1263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1263
def independentCachedBranchMembers1265 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1686,1720,1738,1740,1764,1776,2618,2620,2638,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1265 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1265 2674 5
  · have he : independentCachedBranchMembers1265.erase 2674=independentCachedBranchMembers1259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1259
  · have he : independentCachedBranchMembers1265.filter (independentCachedEdge 2674)=independentCachedBranchMembers1264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1264
def independentCachedBranchMembers1266 : Finset ℕ := ([48,192,1686,1720,1738,1764,1776,2620,2638,2764,2776,3126,3214,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1266 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1266 5 (fun x => (if x<2638 then (if x<1738 then (if x<1686 then (if x<192 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<1776 then (if x<1764 then 0 else 1) else (if x<2620 then 0 else 2))) else (if x<3214 then (if x<2776 then (if x<2764 then 2 else 3) else (if x<3126 then 2 else 3)) else (if x<3270 then (if x<3252 then 3 else 1) else (if x<3282 then 1 else (if x<3304 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1267 : Finset ℕ := ([192,1776,2620,2638,2776,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1267 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1267 4 (fun x => (if x<2776 then (if x<2620 then (if x<1776 then 0 else 0) else (if x<2638 then 1 else 1)) else (if x<3270 then (if x<3252 then 0 else 1) else (if x<3304 then 1 else 0))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1268 : Finset ℕ := ([48,192,1650,1686,1720,1738,1764,1776,2620,2638,2764,2776,3126,3214,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1268 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1268 1650 4
  · have he : independentCachedBranchMembers1268.erase 1650=independentCachedBranchMembers1266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1266
  · have he : independentCachedBranchMembers1268.filter (independentCachedEdge 1650)=independentCachedBranchMembers1267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1267
def independentCachedBranchMembers1269 : Finset ℕ := ([48,192,3126,3214,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1269 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1269 4 (fun x => (if x<3252 then (if x<3126 then (if x<192 then 0 else 0) else (if x<3214 then 0 else 1)) else (if x<3282 then (if x<3270 then 1 else 0) else (if x<3304 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1270 : Finset ℕ := ([48,192,1628,1650,1686,1720,1738,1764,1776,2620,2638,2764,2776,3126,3214,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1270 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1270 1628 4
  · have he : independentCachedBranchMembers1270.erase 1628=independentCachedBranchMembers1268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1268
  · have he : independentCachedBranchMembers1270.filter (independentCachedEdge 1628)=independentCachedBranchMembers1269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1269
def independentCachedBranchMembers1271 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1686,1720,1738,1740,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1271 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1271 2652 5
  · have he : independentCachedBranchMembers1271.erase 2652=independentCachedBranchMembers1265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1265
  · have he : independentCachedBranchMembers1271.filter (independentCachedEdge 2652)=independentCachedBranchMembers1270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1270
def independentCachedBranchMembers1272 : Finset ℕ := ([12,192,1596,1628,1650,1738,1764,1776,2618,2638,2710,2732,2764,2776,3102,3228,3250,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1272 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1272 5 (fun x => (if x<2710 then (if x<1738 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1628 then 0 else (if x<1650 then 1 else 1))) else (if x<1776 then (if x<1764 then 1 else 1) else (if x<2618 then 0 else (if x<2638 then 2 else 2)))) else (if x<3228 then (if x<2764 then (if x<2732 then 2 else 2) else (if x<2776 then 1 else (if x<3102 then 2 else 0))) else (if x<3270 then (if x<3250 then 3 else 3) else (if x<3282 then 3 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1273 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1652,1686,1720,1738,1740,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1273 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1273 1652 5
  · have he : independentCachedBranchMembers1273.erase 1652=independentCachedBranchMembers1271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1271
  · have he : independentCachedBranchMembers1273.filter (independentCachedEdge 1652)=independentCachedBranchMembers1272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1272
def independentCachedBranchMembers1274 : Finset ℕ := ([12,48,1628,1720,1738,1740,1776,2618,2620,2638,2674,2710,2732,2776,2788,3102,3180,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1274 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1274 5 (fun x => (if x<2674 then (if x<1740 then (if x<1628 then (if x<48 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 1 else 1))) else (if x<2618 then (if x<1776 then 0 else 0) else (if x<2620 then 2 else (if x<2638 then 1 else 0)))) else (if x<3102 then (if x<2732 then (if x<2710 then 0 else 2) else (if x<2776 then 2 else (if x<2788 then 1 else 3))) else (if x<3250 then (if x<3180 then 3 else (if x<3214 then 3 else 0)) else (if x<3252 then 0 else (if x<3270 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1275 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1652,1686,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1275 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1275 1752 5
  · have he : independentCachedBranchMembers1275.erase 1752=independentCachedBranchMembers1273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1273
  · have he : independentCachedBranchMembers1275.filter (independentCachedEdge 1752)=independentCachedBranchMembers1274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1274
def independentCachedBranchMembers1276 : Finset ℕ := ([48,192,1596,1650,1720,1740,1764,2618,2638,2652,2710,2732,2762,2776,2800,3102,3126,3192,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1276 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1276 5 (fun x => (if x<2710 then (if x<1740 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1650 then 0 else (if x<1720 then 1 else 1))) else (if x<2618 then (if x<1764 then 0 else 1) else (if x<2638 then 0 else (if x<2652 then 2 else 3)))) else (if x<3102 then (if x<2762 then (if x<2732 then 2 else 1) else (if x<2776 then 0 else (if x<2800 then 2 else 1))) else (if x<3250 then (if x<3126 then 3 else (if x<3192 then 0 else 3)) else (if x<3270 then 3 else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1277 : Finset ℕ := ([12,48,192,252,1596,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1277 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1277 1708 5
  · have he : independentCachedBranchMembers1277.erase 1708=independentCachedBranchMembers1275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1275
  · have he : independentCachedBranchMembers1277.filter (independentCachedEdge 1708)=independentCachedBranchMembers1276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1276
def independentCachedBranchMembers1278 : Finset ℕ := ([192,252,1628,1720,1738,1740,1776,2618,2620,2638,2674,2710,2732,2776,2788,3126,3192,3228,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1278 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1278 5 (fun x => (if x<2674 then (if x<1740 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 1 else 1))) else (if x<2618 then (if x<1776 then 0 else 0) else (if x<2620 then 2 else (if x<2638 then 1 else 1)))) else (if x<3126 then (if x<2732 then (if x<2710 then 3 else 2) else (if x<2776 then 2 else (if x<2788 then 0 else 0))) else (if x<3282 then (if x<3192 then 3 else (if x<3228 then 3 else 3)) else (if x<3284 then 3 else (if x<3304 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1279 : Finset ℕ := ([12,48,192,252,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1279 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1279 1614 5
  · have he : independentCachedBranchMembers1279.erase 1614=independentCachedBranchMembers1277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1277
  · have he : independentCachedBranchMembers1279.filter (independentCachedEdge 1614)=independentCachedBranchMembers1278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1278
end EntropyDesigns.QuadraticRefinement
