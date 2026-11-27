/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch16
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2176 : Finset ℕ := ([12,132,222,252,1596,1628,1678,1686,1708,1740,1748,2606,2646,2668,2716,2758,2788,3102,3164,3214,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2176 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2176 5 (fun x => (if x<2646 then (if x<1678 then (if x<252 then (if x<132 then 0 else (if x<222 then 1 else 0)) else (if x<1596 then 1 else (if x<1628 then 2 else 0))) else (if x<1740 then (if x<1686 then 0 else (if x<1708 then 2 else 1)) else (if x<1748 then 2 else (if x<2606 then 1 else 3)))) else (if x<3164 then (if x<2758 then (if x<2668 then 3 else (if x<2716 then 2 else 0)) else (if x<2788 then 2 else (if x<3102 then 1 else 0))) else (if x<3252 then (if x<3214 then 4 else (if x<3244 then 4 else 3)) else (if x<3276 then 1 else (if x<3284 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2177 : Finset ℕ := ([12,252,1596,1628,1686,1708,1740,2606,2788,3102,3214,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2177 4 (fun x => (if x<1740 then (if x<1628 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1686 then 1 else (if x<1708 then 1 else 1))) else (if x<3102 then (if x<2606 then 0 else (if x<2788 then 2 else 2)) else (if x<3252 then (if x<3214 then 2 else 3) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2178 : Finset ℕ := ([12,132,222,252,1596,1628,1678,1686,1708,1740,1748,2606,2646,2668,2716,2758,2788,3102,3164,3214,3222,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2178 3222 4
  · have he : independentCachedBranchMembers2178.erase 3222=independentCachedBranchMembers2176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2176
  · have he : independentCachedBranchMembers2178.filter (independentCachedEdge 3222)=independentCachedBranchMembers2177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2177
def independentCachedBranchMembers2179 : Finset ℕ := ([132,222,1596,1678,1686,1740,1748,2646,2788,3102,3164,3244,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2179 4 (fun x => (if x<1748 then (if x<1678 then (if x<222 then 0 else (if x<1596 then 0 else 1)) else (if x<1686 then 0 else (if x<1740 then 1 else 1))) else (if x<3102 then (if x<2646 then 0 else (if x<2788 then 2 else 2)) else (if x<3244 then (if x<3164 then 2 else 3) else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2180 : Finset ℕ := ([12,132,222,252,1596,1628,1678,1686,1708,1740,1748,2606,2646,2668,2716,2758,2788,3102,3132,3164,3214,3222,3244,3252,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2180 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2180 3132 4
  · have he : independentCachedBranchMembers2180.erase 3132=independentCachedBranchMembers2178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2178
  · have he : independentCachedBranchMembers2180.filter (independentCachedEdge 3132)=independentCachedBranchMembers2179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2179
def independentCachedBranchMembers2181 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3132,3150,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2181 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2181 2662 5
  · have he : independentCachedBranchMembers2181.erase 2662=independentCachedBranchMembers2175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2175
  · have he : independentCachedBranchMembers2181.filter (independentCachedEdge 2662)=independentCachedBranchMembers2180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2180
def independentCachedBranchMembers2182 : Finset ℕ := ([12,132,252,1596,1644,1678,1692,1702,1740,1764,2606,2620,2646,2668,2702,2716,2740,2764,2788,3102,3150,3164,3188,3222,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2182 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2182 5 (fun x => (if x<2668 then (if x<1692 then (if x<1596 then (if x<132 then 0 else (if x<252 then 1 else 0)) else (if x<1644 then 0 else (if x<1678 then 2 else 1))) else (if x<1764 then (if x<1702 then 2 else (if x<1740 then 2 else 0)) else (if x<2620 then (if x<2606 then 1 else 3) else (if x<2646 then 4 else 3)))) else (if x<3150 then (if x<2740 then (if x<2702 then 0 else (if x<2716 then 4 else 0)) else (if x<2788 then (if x<2764 then 3 else 1) else (if x<3102 then 4 else 4))) else (if x<3222 then (if x<3164 then 3 else (if x<3188 then 0 else 4)) else (if x<3270 then (if x<3244 then 2 else 0) else (if x<3284 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2183 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2183 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2183 3158 5
  · have he : independentCachedBranchMembers2183.erase 3158=independentCachedBranchMembers2181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2181
  · have he : independentCachedBranchMembers2183.filter (independentCachedEdge 3158)=independentCachedBranchMembers2182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2182
def independentCachedBranchMembers2184 : Finset ℕ := ([132,222,252,1628,1652,1686,1692,1734,1740,1764,2606,2646,2652,2710,2716,2740,2758,2764,2788,3102,3132,3150,3180,3214,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2184 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2184 5 (fun x => (if x<2710 then (if x<1692 then (if x<1628 then (if x<222 then 0 else (if x<252 then 0 else 1)) else (if x<1652 then 1 else (if x<1686 then 2 else 0))) else (if x<1764 then (if x<1734 then 2 else (if x<1740 then 2 else 0)) else (if x<2646 then (if x<2606 then 1 else 3) else (if x<2652 then 3 else 4)))) else (if x<3132 then (if x<2758 then (if x<2716 then 4 else (if x<2740 then 0 else 3)) else (if x<2788 then (if x<2764 then 0 else 1) else (if x<3102 then 4 else 4))) else (if x<3214 then (if x<3150 then 2 else (if x<3180 then 3 else 1)) else (if x<3244 then (if x<3238 then 0 else 4) else (if x<3284 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2185 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3118,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2185 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2185 3118 5
  · have he : independentCachedBranchMembers2185.erase 3118=independentCachedBranchMembers2183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2183
  · have he : independentCachedBranchMembers2185.filter (independentCachedEdge 3118)=independentCachedBranchMembers2184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2184
def independentCachedBranchMembers2186 : Finset ℕ := ([132,252,1596,1614,1686,1692,1708,1748,1764,2606,2646,2652,2668,2702,2740,2758,2764,3132,3150,3188,3222,3228,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2186 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2186 5 (fun x => (if x<2668 then (if x<1708 then (if x<1614 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1686 then 1 else (if x<1692 then 1 else 0))) else (if x<2606 then (if x<1748 then 2 else (if x<1764 then 2 else 0)) else (if x<2646 then 2 else (if x<2652 then 2 else 3)))) else (if x<3150 then (if x<2758 then (if x<2702 then 1 else (if x<2740 then 3 else 0)) else (if x<2764 then 1 else (if x<3132 then 0 else 4))) else (if x<3228 then (if x<3188 then 3 else (if x<3222 then 3 else 4)) else (if x<3244 then (if x<3238 then 3 else 3) else (if x<3284 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2187 : Finset ℕ := ([252,1686,1708,1764,2646,2668,2764,3132,3150,3188,3228,3238,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2187 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2187 4 (fun x => (if x<2764 then (if x<1764 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<2646 then 1 else (if x<2668 then 2 else 0))) else (if x<3188 then (if x<3132 then 2 else (if x<3150 then 0 else 2)) else (if x<3238 then (if x<3228 then 3 else 3) else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2188 : Finset ℕ := ([132,252,1596,1614,1686,1692,1702,1708,1748,1764,2606,2646,2652,2668,2702,2740,2758,2764,3132,3150,3188,3222,3228,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2188 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2188 1702 4
  · have he : independentCachedBranchMembers2188.erase 1702=independentCachedBranchMembers2186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2186
  · have he : independentCachedBranchMembers2188.filter (independentCachedEdge 1702)=independentCachedBranchMembers2187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2187
def independentCachedBranchMembers2189 : Finset ℕ := ([132,1596,1748,1764,2606,2758,2764,3150,3188,3222,3228,3238,3244] : List ℕ).toFinset
theorem independentCachedBranchBound2189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2189 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2189 4 (fun x => (if x<2764 then (if x<1764 then (if x<1596 then 0 else (if x<1748 then 1 else 0)) else (if x<2606 then 1 else (if x<2758 then 2 else 0))) else (if x<3222 then (if x<3150 then 2 else (if x<3188 then 2 else 1)) else (if x<3238 then (if x<3228 then 0 else 3) else (if x<3244 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2190 : Finset ℕ := ([132,252,1596,1614,1652,1686,1692,1702,1708,1748,1764,2606,2646,2652,2668,2702,2740,2758,2764,3132,3150,3188,3222,3228,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2190 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2190 1652 4
  · have he : independentCachedBranchMembers2190.erase 1652=independentCachedBranchMembers2188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2188
  · have he : independentCachedBranchMembers2190.filter (independentCachedEdge 1652)=independentCachedBranchMembers2189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2189
def independentCachedBranchMembers2191 : Finset ℕ := ([132,252,1596,1686,1708,1748,2606,2646,2668,2758,3132,3222,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2191 4 (fun x => (if x<2646 then (if x<1686 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1748 then (if x<1708 then 1 else 0) else (if x<2606 then 0 else 2))) else (if x<3132 then (if x<2668 then 2 else (if x<2758 then 1 else 1)) else (if x<3244 then (if x<3222 then 3 else 3) else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2192 : Finset ℕ := ([132,252,1596,1614,1652,1686,1692,1702,1708,1748,1764,2606,2646,2652,2662,2668,2702,2740,2758,2764,3132,3150,3188,3222,3228,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2192 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2192 2662 4
  · have he : independentCachedBranchMembers2192.erase 2662=independentCachedBranchMembers2190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2190
  · have he : independentCachedBranchMembers2192.filter (independentCachedEdge 2662)=independentCachedBranchMembers2191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2191
def independentCachedBranchMembers2193 : Finset ℕ := ([132,252,1596,1652,1686,1702,2652,2668,2702,2758,3150,3228,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2193 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2193 4 (fun x => (if x<2668 then (if x<1652 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1702 then (if x<1686 then 2 else 1) else (if x<2652 then 2 else 2))) else (if x<3150 then (if x<2702 then 1 else (if x<2758 then 2 else 1)) else (if x<3244 then (if x<3228 then 3 else 0) else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2194 : Finset ℕ := ([132,252,1590,1596,1614,1652,1686,1692,1702,1708,1748,1764,2606,2646,2652,2662,2668,2702,2740,2758,2764,3132,3150,3188,3222,3228,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2194 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2194 1590 4
  · have he : independentCachedBranchMembers2194.erase 1590=independentCachedBranchMembers2192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2192
  · have he : independentCachedBranchMembers2194.filter (independentCachedEdge 1590)=independentCachedBranchMembers2193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2193
def independentCachedBranchMembers2195 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2620,2638,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3118,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2195 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2195 2638 5
  · have he : independentCachedBranchMembers2195.erase 2638=independentCachedBranchMembers2185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2185
  · have he : independentCachedBranchMembers2195.filter (independentCachedEdge 2638)=independentCachedBranchMembers2194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2194
def independentCachedBranchMembers2196 : Finset ℕ := ([12,132,222,252,1590,1628,1644,1678,1692,1708,1734,1748,1764,2606,2620,2646,2662,2710,2740,2764,3150,3180,3228,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2196 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2196 5 (fun x => (if x<2606 then (if x<1644 then (if x<252 then (if x<132 then 0 else (if x<222 then 1 else 0)) else (if x<1590 then 1 else (if x<1628 then 2 else 0))) else (if x<1708 then (if x<1678 then 2 else (if x<1692 then 0 else 1)) else (if x<1748 then (if x<1734 then 3 else 2) else (if x<1764 then 3 else 1)))) else (if x<2764 then (if x<2662 then (if x<2620 then 3 else (if x<2646 then 2 else 3)) else (if x<2710 then 2 else (if x<2740 then 2 else 1))) else (if x<3228 then (if x<3150 then 0 else (if x<3180 then 0 else 4)) else (if x<3270 then (if x<3244 then 0 else 1) else (if x<3284 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2197 : Finset ℕ := ([132,252,1628,1644,1678,1734,2620,2710,3150,3228,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2197 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2197 4 (fun x => (if x<2620 then (if x<1644 then (if x<252 then 0 else (if x<1628 then 0 else 1)) else (if x<1678 then 2 else (if x<1734 then 1 else 2))) else (if x<3228 then (if x<2710 then 2 else (if x<3150 then 2 else 1)) else (if x<3244 then 0 else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2198 : Finset ℕ := ([12,132,222,252,1590,1614,1628,1644,1678,1692,1708,1734,1748,1764,2606,2620,2646,2662,2710,2740,2764,3150,3180,3228,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2198 1614 4
  · have he : independentCachedBranchMembers2198.erase 1614=independentCachedBranchMembers2196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2196
  · have he : independentCachedBranchMembers2198.filter (independentCachedEdge 1614)=independentCachedBranchMembers2197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2197
def independentCachedBranchMembers2199 : Finset ℕ := ([252,1590,1628,1644,1678,1748,1764,2620,2646,2662,2740,3150,3228,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2199 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2199 4 (fun x => (if x<2620 then (if x<1644 then (if x<1590 then 0 else (if x<1628 then 1 else 0)) else (if x<1748 then (if x<1678 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3150 then (if x<2662 then (if x<2646 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3244 then (if x<3228 then 3 else 3) else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2200 : Finset ℕ := ([12,132,222,252,1590,1614,1628,1644,1678,1692,1708,1734,1748,1764,2606,2620,2646,2662,2710,2740,2764,3150,3180,3214,3228,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2200 3214 4
  · have he : independentCachedBranchMembers2200.erase 3214=independentCachedBranchMembers2198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2198
  · have he : independentCachedBranchMembers2200.filter (independentCachedEdge 3214)=independentCachedBranchMembers2199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2199
def independentCachedBranchMembers2201 : Finset ℕ := ([132,1590,1628,1678,1708,1734,1764,2606,2662,2710,2740,3150,3180,3228,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2201 4 (fun x => (if x<2606 then (if x<1678 then (if x<1590 then 0 else (if x<1628 then 1 else 1)) else (if x<1734 then (if x<1708 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<3150 then (if x<2710 then (if x<2662 then 2 else 3) else (if x<2740 then 2 else 3)) else (if x<3228 then (if x<3180 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2202 : Finset ℕ := ([12,132,222,252,1590,1614,1628,1644,1678,1692,1708,1734,1748,1764,2606,2620,2646,2662,2710,2740,2764,3150,3164,3180,3214,3228,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2202 3164 4
  · have he : independentCachedBranchMembers2202.erase 3164=independentCachedBranchMembers2200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2200
  · have he : independentCachedBranchMembers2202.filter (independentCachedEdge 3164)=independentCachedBranchMembers2201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2201
def independentCachedBranchMembers2203 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2614,2620,2638,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3118,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2203 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2203 2614 5
  · have he : independentCachedBranchMembers2203.erase 2614=independentCachedBranchMembers2195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2195
  · have he : independentCachedBranchMembers2203.filter (independentCachedEdge 2614)=independentCachedBranchMembers2202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2202
def independentCachedBranchMembers2204 : Finset ℕ := ([132,252,1590,1614,1628,1652,1686,1708,1734,1748,2606,2620,2646,2702,2716,2740,2764,2788,3132,3158,3180,3214,3228,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2204 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2204 5 (fun x => (if x<2702 then (if x<1686 then (if x<1614 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1628 then 1 else (if x<1652 then 2 else 3))) else (if x<1748 then (if x<1708 then 2 else (if x<1734 then 0 else 3)) else (if x<2620 then (if x<2606 then 0 else 1) else (if x<2646 then 3 else 1)))) else (if x<3158 then (if x<2764 then (if x<2716 then 3 else (if x<2740 then 0 else 1)) else (if x<2788 then 1 else (if x<3132 then 0 else 4))) else (if x<3228 then (if x<3180 then 2 else (if x<3214 then 2 else 4)) else (if x<3252 then (if x<3238 then 2 else 2) else (if x<3276 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2205 : Finset ℕ := ([132,1590,1652,1686,1734,1748,2646,2740,2788,3158,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2205 4 (fun x => (if x<2646 then (if x<1686 then (if x<1590 then 0 else (if x<1652 then 1 else 2)) else (if x<1734 then 0 else (if x<1748 then 1 else 3))) else (if x<3158 then (if x<2740 then 1 else (if x<2788 then 0 else 2)) else (if x<3238 then 3 else (if x<3252 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2206 : Finset ℕ := ([12,132,252,1590,1614,1628,1652,1686,1708,1734,1748,2606,2620,2646,2702,2716,2740,2764,2788,3132,3158,3180,3214,3228,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2206 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2206 12 4
  · have he : independentCachedBranchMembers2206.erase 12=independentCachedBranchMembers2204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2204
  · have he : independentCachedBranchMembers2206.filter (independentCachedEdge 12)=independentCachedBranchMembers2205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2205
def independentCachedBranchMembers2207 : Finset ℕ := ([132,1590,1734,1748,2606,2620,2764,2788,3158,3180,3214,3228,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2207 4 (fun x => (if x<2788 then (if x<1748 then (if x<1590 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then (if x<2606 then 1 else 1) else (if x<2764 then 2 else 0))) else (if x<3214 then (if x<3158 then 2 else (if x<3180 then 3 else 2)) else (if x<3238 then (if x<3228 then 0 else 3) else (if x<3252 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2208 : Finset ℕ := ([12,132,252,1590,1614,1628,1652,1686,1708,1734,1748,2606,2620,2646,2668,2702,2716,2740,2764,2788,3132,3158,3180,3214,3228,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2208 2668 4
  · have he : independentCachedBranchMembers2208.erase 2668=independentCachedBranchMembers2206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2206
  · have he : independentCachedBranchMembers2208.filter (independentCachedEdge 2668)=independentCachedBranchMembers2207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2207
def independentCachedBranchMembers2209 : Finset ℕ := ([252,1628,1652,1686,1734,2606,2646,2716,2740,2764,2788,3132,3180,3214,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2209 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2209 4 (fun x => (if x<2716 then (if x<1686 then (if x<1628 then 0 else (if x<1652 then 0 else 1)) else (if x<2606 then (if x<1734 then 1 else 2) else (if x<2646 then 3 else 1))) else (if x<3132 then (if x<2764 then (if x<2740 then 0 else 1) else (if x<2788 then 2 else 3)) else (if x<3214 then (if x<3180 then 0 else 3) else (if x<3238 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2210 : Finset ℕ := ([1628,1652,2606,2646,3132,3180] : List ℕ).toFinset
theorem independentCachedBranchBound2210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2210 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2210 3 (fun x => (if x<2646 then (if x<1652 then 0 else (if x<2606 then 1 else 2)) else (if x<3132 then 0 else (if x<3180 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2211 : Finset ℕ := ([132,252,1628,1652,1686,1734,2606,2646,2716,2740,2764,2788,3132,3180,3214,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2211 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2211 132 3
  · have he : independentCachedBranchMembers2211.erase 132=independentCachedBranchMembers2209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2209
  · have he : independentCachedBranchMembers2211.filter (independentCachedEdge 132)=independentCachedBranchMembers2210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2210
def independentCachedBranchMembers2212 : Finset ℕ := ([12,132,252,1590,1614,1628,1652,1686,1708,1734,1748,2606,2620,2646,2668,2702,2716,2740,2764,2788,3118,3132,3158,3180,3214,3228,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2212 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2212 3118 4
  · have he : independentCachedBranchMembers2212.erase 3118=independentCachedBranchMembers2208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2208
  · have he : independentCachedBranchMembers2212.filter (independentCachedEdge 3118)=independentCachedBranchMembers2211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2211
def independentCachedBranchMembers2213 : Finset ℕ := ([12,132,222,252,1590,1596,1614,1622,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2614,2620,2638,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3118,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2213 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2213 1622 5
  · have he : independentCachedBranchMembers2213.erase 1622=independentCachedBranchMembers2203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2203
  · have he : independentCachedBranchMembers2213.filter (independentCachedEdge 1622)=independentCachedBranchMembers2212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2212
def independentCachedBranchMembers2214 : Finset ℕ := ([132,252,1590,1596,1614,1644,1678,1702,1708,1748,2606,2646,2652,2710,2716,2740,2764,2788,3118,3164,3188,3222,3228,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2214 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2214 5 (fun x => (if x<2710 then (if x<1678 then (if x<1596 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1614 then 2 else (if x<1644 then 1 else 3))) else (if x<1748 then (if x<1702 then 2 else (if x<1708 then 3 else 0)) else (if x<2646 then (if x<2606 then 0 else 1) else (if x<2652 then 1 else 3)))) else (if x<3164 then (if x<2764 then (if x<2716 then 3 else (if x<2740 then 0 else 1)) else (if x<2788 then 1 else (if x<3118 then 0 else 2))) else (if x<3228 then (if x<3188 then 4 else (if x<3222 then 2 else 4)) else (if x<3270 then (if x<3252 then 2 else 0) else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2215 : Finset ℕ := ([252,1590,1596,1644,1702,1708,2606,2740,2788,3118,3188,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2215 4 (fun x => (if x<2606 then (if x<1644 then (if x<1590 then 0 else (if x<1596 then 1 else 0)) else (if x<1702 then 1 else (if x<1708 then 2 else 3))) else (if x<3118 then (if x<2740 then 1 else (if x<2788 then 0 else 2)) else (if x<3188 then 3 else (if x<3252 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2216 : Finset ℕ := ([132,222,252,1590,1596,1614,1644,1678,1702,1708,1748,2606,2646,2652,2710,2716,2740,2764,2788,3118,3164,3188,3222,3228,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2216 222 4
  · have he : independentCachedBranchMembers2216.erase 222=independentCachedBranchMembers2214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2214
  · have he : independentCachedBranchMembers2216.filter (independentCachedEdge 222)=independentCachedBranchMembers2215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2215
def independentCachedBranchMembers2217 : Finset ℕ := ([252,1590,1644,1708,2646,2710,2764,2788,3118,3164,3188,3228,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2217 4 (fun x => (if x<2788 then (if x<1708 then (if x<1590 then 0 else (if x<1644 then 1 else 0)) else (if x<2710 then (if x<2646 then 1 else 1) else (if x<2764 then 2 else 0))) else (if x<3188 then (if x<3118 then 2 else (if x<3164 then 3 else 0)) else (if x<3252 then (if x<3228 then 3 else 3) else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2218 : Finset ℕ := ([132,222,252,1590,1596,1614,1644,1678,1702,1708,1748,2606,2646,2652,2710,2716,2740,2758,2764,2788,3118,3164,3188,3222,3228,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2218 2758 4
  · have he : independentCachedBranchMembers2218.erase 2758=independentCachedBranchMembers2216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2216
  · have he : independentCachedBranchMembers2218.filter (independentCachedEdge 2758)=independentCachedBranchMembers2217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2217
def independentCachedBranchMembers2219 : Finset ℕ := ([252,1596,1644,1678,1702,2606,2646,2716,2740,2764,2788,3164,3188,3222,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2219 4 (fun x => (if x<2716 then (if x<1678 then (if x<1596 then 0 else (if x<1644 then 0 else 1)) else (if x<2606 then (if x<1702 then 1 else 2) else (if x<2646 then 1 else 3))) else (if x<3164 then (if x<2764 then (if x<2740 then 0 else 2) else (if x<2788 then 1 else 3)) else (if x<3222 then (if x<3188 then 0 else 3) else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2220 : Finset ℕ := ([1596,1644,2606,2646,3164,3188] : List ℕ).toFinset
theorem independentCachedBranchBound2220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2220 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2220 3 (fun x => (if x<2646 then (if x<1644 then 0 else (if x<2606 then 1 else 0)) else (if x<3164 then 2 else (if x<3188 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2221 : Finset ℕ := ([132,252,1596,1644,1678,1702,2606,2646,2716,2740,2764,2788,3164,3188,3222,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2221 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2221 132 3
  · have he : independentCachedBranchMembers2221.erase 132=independentCachedBranchMembers2219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2219
  · have he : independentCachedBranchMembers2221.filter (independentCachedEdge 132)=independentCachedBranchMembers2220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2220
def independentCachedBranchMembers2222 : Finset ℕ := ([132,222,252,1590,1596,1614,1644,1678,1702,1708,1748,2606,2646,2652,2710,2716,2740,2758,2764,2788,3118,3158,3164,3188,3222,3228,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2222 3158 4
  · have he : independentCachedBranchMembers2222.erase 3158=independentCachedBranchMembers2218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2218
  · have he : independentCachedBranchMembers2222.filter (independentCachedEdge 3158)=independentCachedBranchMembers2221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2221
def independentCachedBranchMembers2223 : Finset ℕ := ([12,132,222,252,1582,1590,1596,1614,1622,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2614,2620,2638,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3118,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2223 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2223 1582 5
  · have he : independentCachedBranchMembers2223.erase 1582=independentCachedBranchMembers2213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2213
  · have he : independentCachedBranchMembers2223.filter (independentCachedEdge 1582)=independentCachedBranchMembers2222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2222
def independentCachedBranchMembers2224 : Finset ℕ := ([12,222,1582,1596,1622,1628,1678,1686,1692,1764,2614,2620,2638,2652,2702,2710,2716,2788,3102,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2224 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2224 5 (fun x => (if x<2652 then (if x<1678 then (if x<1596 then (if x<222 then 0 else (if x<1582 then 0 else 1)) else (if x<1622 then 2 else (if x<1628 then 1 else 0))) else (if x<1764 then (if x<1686 then 0 else (if x<1692 then 2 else 1)) else (if x<2620 then (if x<2614 then 1 else 2) else (if x<2638 then 3 else 0)))) else (if x<3188 then (if x<2716 then (if x<2702 then 4 else (if x<2710 then 3 else 4)) else (if x<3102 then (if x<2788 then 0 else 3) else (if x<3180 then 0 else 4))) else (if x<3252 then (if x<3238 then 3 else (if x<3244 then 4 else 1)) else (if x<3276 then (if x<3270 then 2 else 3) else (if x<3284 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2225 : Finset ℕ := ([1582,1622,1628,1678,2620,2638,2710,2788,3188,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2225 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2225 4 (fun x => (if x<2710 then (if x<1678 then (if x<1622 then 0 else (if x<1628 then 0 else 1)) else (if x<2620 then 1 else (if x<2638 then 2 else 0))) else (if x<3238 then (if x<2788 then 2 else (if x<3188 then 2 else 1)) else (if x<3244 then 1 else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2226 : Finset ℕ := ([1582,1622,2620,2710,3188,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2226 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2226 3 (fun x => (if x<2710 then (if x<1622 then 0 else (if x<2620 then 0 else 1)) else (if x<3188 then 1 else (if x<3238 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2227 : Finset ℕ := ([1582,1622,1628,1678,2620,2638,2710,2716,2788,3188,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2227 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2227 2716 3
  · have he : independentCachedBranchMembers2227.erase 2716=independentCachedBranchMembers2225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2225
  · have he : independentCachedBranchMembers2227.filter (independentCachedEdge 2716)=independentCachedBranchMembers2226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2226
def independentCachedBranchMembers2228 : Finset ℕ := ([1628,1678,2620,2710,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2228 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2228 3 (fun x => (if x<2710 then (if x<1678 then 0 else (if x<2620 then 0 else 1)) else (if x<3244 then 1 else (if x<3284 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2229 : Finset ℕ := ([1582,1622,1628,1678,2614,2620,2638,2710,2716,2788,3188,3238,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2229 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2229 2614 3
  · have he : independentCachedBranchMembers2229.erase 2614=independentCachedBranchMembers2227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2227
  · have he : independentCachedBranchMembers2229.filter (independentCachedEdge 2614)=independentCachedBranchMembers2228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2228
def independentCachedBranchMembers2230 : Finset ℕ := ([12,222,1582,1596,1614,1622,1628,1678,1686,1692,1764,2614,2620,2638,2652,2702,2710,2716,2788,3102,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2230 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2230 1614 4
  · have he : independentCachedBranchMembers2230.erase 1614=independentCachedBranchMembers2224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2224
  · have he : independentCachedBranchMembers2230.filter (independentCachedEdge 1614)=independentCachedBranchMembers2229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2229
def independentCachedBranchMembers2231 : Finset ℕ := ([12,1582,1596,1622,1678,1692,1764,2614,2638,2652,2710,3180,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2231 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2231 4 (fun x => (if x<2614 then (if x<1622 then (if x<1582 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then (if x<1678 then 1 else 1) else (if x<1764 then 0 else 1))) else (if x<3180 then (if x<2652 then (if x<2638 then 2 else 2) else (if x<2710 then 3 else 3)) else (if x<3252 then (if x<3238 then 3 else 3) else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2232 : Finset ℕ := ([12,222,1582,1596,1614,1622,1628,1678,1686,1692,1764,2614,2620,2638,2646,2652,2702,2710,2716,2788,3102,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2232 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2232 2646 4
  · have he : independentCachedBranchMembers2232.erase 2646=independentCachedBranchMembers2230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2230
  · have he : independentCachedBranchMembers2232.filter (independentCachedEdge 2646)=independentCachedBranchMembers2231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2231
def independentCachedBranchMembers2233 : Finset ℕ := ([222,1582,1622,1628,1686,1692,1764,2614,2620,2638,2702,3188,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2233 4 (fun x => (if x<2614 then (if x<1628 then (if x<1582 then 0 else (if x<1622 then 1 else 0)) else (if x<1692 then (if x<1686 then 1 else 1) else (if x<1764 then 0 else 1))) else (if x<3188 then (if x<2638 then (if x<2620 then 2 else 3) else (if x<2702 then 2 else 3)) else (if x<3270 then (if x<3252 then 3 else 2) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2234 : Finset ℕ := ([12,222,1582,1596,1614,1622,1628,1678,1686,1692,1764,2606,2614,2620,2638,2646,2652,2702,2710,2716,2788,3102,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2234 2606 4
  · have he : independentCachedBranchMembers2234.erase 2606=independentCachedBranchMembers2232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2232
  · have he : independentCachedBranchMembers2234.filter (independentCachedEdge 2606)=independentCachedBranchMembers2233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2233
def independentCachedBranchMembers2235 : Finset ℕ := ([222,1582,1596,1622,1686,2614,2638,2652,2702,2716,2788,3180,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2235 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2235 4 (fun x => (if x<2652 then (if x<1622 then (if x<1582 then 0 else (if x<1596 then 1 else 2)) else (if x<2614 then (if x<1686 then 0 else 1) else (if x<2638 then 1 else 0))) else (if x<3180 then (if x<2716 then (if x<2702 then 2 else 1) else (if x<2788 then 3 else 3)) else (if x<3270 then (if x<3244 then 2 else 3) else (if x<3284 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2236 : Finset ℕ := ([1622,1686,2614,2788,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2236 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2236 3 (fun x => (if x<2788 then (if x<1686 then 0 else (if x<2614 then 1 else 0)) else (if x<3270 then 2 else (if x<3284 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2237 : Finset ℕ := ([12,222,1582,1596,1622,1686,2614,2638,2652,2702,2716,2788,3180,3244,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2237 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2237 12 3
  · have he : independentCachedBranchMembers2237.erase 12=independentCachedBranchMembers2235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2235
  · have he : independentCachedBranchMembers2237.filter (independentCachedEdge 12)=independentCachedBranchMembers2236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2236
def independentCachedBranchMembers2238 : Finset ℕ := ([12,222,1582,1590,1596,1614,1622,1628,1678,1686,1692,1764,2606,2614,2620,2638,2646,2652,2702,2710,2716,2788,3102,3180,3188,3238,3244,3252,3270,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2238 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2238 1590 4
  · have he : independentCachedBranchMembers2238.erase 1590=independentCachedBranchMembers2234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2234
  · have he : independentCachedBranchMembers2238.filter (independentCachedEdge 1590)=independentCachedBranchMembers2237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2237
def independentCachedBranchMembers2239 : Finset ℕ := ([12,132,222,252,1582,1590,1596,1614,1622,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2614,2620,2638,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3118,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2239 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2239 3300 5
  · have he : independentCachedBranchMembers2239.erase 3300=independentCachedBranchMembers2223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2223
  · have he : independentCachedBranchMembers2239.filter (independentCachedEdge 3300)=independentCachedBranchMembers2238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2238
def independentCachedBranchMembers2240 : Finset ℕ := ([132,222,252,1590,1628,1644,1678,1692,1708,1734,1748,2614,2638,2652,2702,2716,2732,2772,2788,3102,3118,3132,3158,3188,3222,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2240 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2240 5 (fun x => (if x<2702 then (if x<1692 then (if x<1590 then (if x<222 then 0 else (if x<252 then 0 else 1)) else (if x<1644 then (if x<1628 then 2 else 1) else (if x<1678 then 2 else 0))) else (if x<1748 then (if x<1708 then 2 else (if x<1734 then 1 else 2)) else (if x<2638 then (if x<2614 then 0 else 3) else (if x<2652 then 3 else 4)))) else (if x<3132 then (if x<2772 then (if x<2716 then 4 else (if x<2732 then 0 else 3)) else (if x<3102 then (if x<2788 then 3 else 4) else (if x<3118 then 4 else 3))) else (if x<3222 then (if x<3158 then 1 else (if x<3188 then 3 else 4)) else (if x<3252 then (if x<3238 then 0 else 4) else (if x<3276 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2241 : Finset ℕ := ([132,1590,1734,1748,2614,2772,2788,3158,3188,3222,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2241 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2241 4 (fun x => (if x<2788 then (if x<1748 then (if x<1590 then 0 else (if x<1734 then 1 else 0)) else (if x<2614 then 1 else (if x<2772 then 2 else 0))) else (if x<3222 then (if x<3158 then 2 else (if x<3188 then 1 else 2)) else (if x<3238 then 0 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2242 : Finset ℕ := ([12,132,222,252,1590,1628,1644,1678,1692,1708,1734,1748,2614,2638,2652,2702,2716,2732,2772,2788,3102,3118,3132,3158,3188,3222,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2242 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2242 12 4
  · have he : independentCachedBranchMembers2242.erase 12=independentCachedBranchMembers2240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2240
  · have he : independentCachedBranchMembers2242.filter (independentCachedEdge 12)=independentCachedBranchMembers2241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2241
def independentCachedBranchMembers2243 : Finset ℕ := ([12,252,1590,1628,1644,1692,1708,1734,2638,2702,2772,2788,3102,3118,3188,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2243 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2243 4 (fun x => (if x<2638 then (if x<1644 then (if x<1590 then (if x<252 then 0 else 0) else (if x<1628 then 1 else 0)) else (if x<1708 then (if x<1692 then 1 else 1) else (if x<1734 then 0 else 1))) else (if x<3102 then (if x<2772 then (if x<2702 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3188 then (if x<3118 then 3 else 2) else (if x<3252 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2244 : Finset ℕ := ([12,132,222,252,1590,1628,1644,1678,1692,1708,1734,1748,2614,2638,2652,2702,2716,2732,2758,2772,2788,3102,3118,3132,3158,3188,3222,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2244 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2244 2758 4
  · have he : independentCachedBranchMembers2244.erase 2758=independentCachedBranchMembers2242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2242
  · have he : independentCachedBranchMembers2244.filter (independentCachedEdge 2758)=independentCachedBranchMembers2243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2243
def independentCachedBranchMembers2245 : Finset ℕ := ([132,222,1590,1644,1678,1692,1734,1748,2638,2652,2732,2788,3102,3158,3238,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2245 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2245 4 (fun x => (if x<2638 then (if x<1678 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1644 then 1 else 1)) else (if x<1734 then (if x<1692 then 0 else 1) else (if x<1748 then 1 else 0))) else (if x<3102 then (if x<2732 then (if x<2652 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3238 then (if x<3158 then 3 else 2) else (if x<3252 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2246 : Finset ℕ := ([12,132,222,252,1590,1628,1644,1678,1692,1708,1734,1748,2614,2638,2652,2668,2702,2716,2732,2758,2772,2788,3102,3118,3132,3158,3188,3222,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2246 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2246 2668 4
  · have he : independentCachedBranchMembers2246.erase 2668=independentCachedBranchMembers2244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2244
  · have he : independentCachedBranchMembers2246.filter (independentCachedEdge 2668)=independentCachedBranchMembers2245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2245
def independentCachedBranchMembers2247 : Finset ℕ := ([222,1644,1708,1734,1748,2614,2638,2652,2702,2716,2788,3118,3132,3158,3222] : List ℕ).toFinset
theorem independentCachedBranchBound2247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2247 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2247 4 (fun x => (if x<2652 then (if x<1734 then (if x<1644 then 0 else (if x<1708 then 1 else 2)) else (if x<2614 then (if x<1748 then 0 else 1) else (if x<2638 then 3 else 0))) else (if x<3118 then (if x<2716 then (if x<2702 then 1 else 2) else (if x<2788 then 3 else 1)) else (if x<3158 then (if x<3132 then 2 else 3) else (if x<3222 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2248 : Finset ℕ := ([1734,1748,2614,2788,3158,3222] : List ℕ).toFinset
theorem independentCachedBranchBound2248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2248 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2248 3 (fun x => (if x<2788 then (if x<1748 then 0 else (if x<2614 then 1 else 2)) else (if x<3158 then 0 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2249 : Finset ℕ := ([12,222,1644,1708,1734,1748,2614,2638,2652,2702,2716,2788,3118,3132,3158,3222] : List ℕ).toFinset
theorem independentCachedBranchBound2249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2249 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2249 12 3
  · have he : independentCachedBranchMembers2249.erase 12=independentCachedBranchMembers2247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2247
  · have he : independentCachedBranchMembers2249.filter (independentCachedEdge 12)=independentCachedBranchMembers2248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2248
def independentCachedBranchMembers2250 : Finset ℕ := ([12,132,222,252,1590,1628,1644,1678,1692,1708,1734,1748,1764,2614,2638,2652,2668,2702,2716,2732,2758,2772,2788,3102,3118,3132,3158,3188,3222,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2250 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2250 1764 4
  · have he : independentCachedBranchMembers2250.erase 1764=independentCachedBranchMembers2246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2246
  · have he : independentCachedBranchMembers2250.filter (independentCachedEdge 1764)=independentCachedBranchMembers2249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2249
def independentCachedBranchMembers2251 : Finset ℕ := ([252,1628,1644,1678,1734,2614,2638,2716,2732,2772,2788,3132,3188,3222,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2251 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2251 4 (fun x => (if x<2716 then (if x<1678 then (if x<1628 then 0 else (if x<1644 then 0 else 1)) else (if x<2614 then (if x<1734 then 1 else 2) else (if x<2638 then 3 else 1))) else (if x<3132 then (if x<2772 then (if x<2732 then 0 else 1) else (if x<2788 then 2 else 3)) else (if x<3222 then (if x<3188 then 0 else 3) else (if x<3238 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2252 : Finset ℕ := ([1628,1644,2614,2638,3132,3188] : List ℕ).toFinset
theorem independentCachedBranchBound2252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2252 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2252 3 (fun x => (if x<2638 then (if x<1644 then 0 else (if x<2614 then 1 else 2)) else (if x<3132 then 0 else (if x<3188 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2253 : Finset ℕ := ([132,252,1628,1644,1678,1734,2614,2638,2716,2732,2772,2788,3132,3188,3222,3238] : List ℕ).toFinset
theorem independentCachedBranchBound2253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2253 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2253 132 3
  · have he : independentCachedBranchMembers2253.erase 132=independentCachedBranchMembers2251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2251
  · have he : independentCachedBranchMembers2253.filter (independentCachedEdge 132)=independentCachedBranchMembers2252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2252
def independentCachedBranchMembers2254 : Finset ℕ := ([12,132,222,252,1590,1614,1628,1644,1678,1692,1708,1734,1748,1764,2614,2638,2652,2668,2702,2716,2732,2758,2772,2788,3102,3118,3132,3158,3188,3222,3238,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2254 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2254 1614 4
  · have he : independentCachedBranchMembers2254.erase 1614=independentCachedBranchMembers2250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2250
  · have he : independentCachedBranchMembers2254.filter (independentCachedEdge 1614)=independentCachedBranchMembers2253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2253
def independentCachedBranchMembers2255 : Finset ℕ := ([12,132,222,252,1582,1590,1596,1614,1622,1628,1644,1652,1678,1686,1692,1702,1708,1734,1740,1748,1764,2606,2614,2620,2638,2646,2652,2662,2668,2702,2710,2716,2732,2740,2758,2764,2772,2788,3102,3118,3126,3132,3150,3158,3164,3180,3188,3214,3222,3228,3238,3244,3252,3270,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2255 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2255 3126 5
  · have he : independentCachedBranchMembers2255.erase 3126=independentCachedBranchMembers2239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2239
  · have he : independentCachedBranchMembers2255.filter (independentCachedEdge 3126)=independentCachedBranchMembers2254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2254
def independentCachedBranchMembers2256 : Finset ℕ := ([12,18,48,72,132,192,222,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2256 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2256 250 6
  · have he : independentCachedBranchMembers2256.erase 250=independentCachedBranchMembers2128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2128
  · have he : independentCachedBranchMembers2256.filter (independentCachedEdge 250)=independentCachedBranchMembers2255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2255
def independentCachedBranchMembers2257 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1708,1748,1752,1764,1768,2606,2618,2646,2650,2716,2740,2764,2788,2792,2800,3102,3126,3162,3178,3244,3256,3276,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2257 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2257 6 (fun x => (if x<2716 then (if x<1748 then (if x<1594 then (if x<192 then (if x<132 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1650 then (if x<1614 then 0 else 2) else (if x<1708 then 2 else 0))) else (if x<2606 then (if x<1764 then (if x<1752 then 1 else 2) else (if x<1768 then 2 else 1)) else (if x<2646 then (if x<2618 then 3 else 4) else (if x<2650 then 3 else 0)))) else (if x<3162 then (if x<2792 then (if x<2764 then (if x<2740 then 3 else 4) else (if x<2788 then 0 else 1)) else (if x<3102 then (if x<2800 then 4 else 2) else (if x<3126 then 3 else 4))) else (if x<3276 then (if x<3244 then (if x<3178 then 5 else 4) else (if x<3256 then 3 else 4)) else (if x<3300 then (if x<3284 then 1 else 3) else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2258 : Finset ℕ := ([18,132,1594,1614,1650,1708,1752,1764,2618,2646,2740,2788,3126,3162,3256,3276,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2258 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2258 5 (fun x => (if x<2646 then (if x<1650 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1614 then 0 else 1)) else (if x<1752 then (if x<1708 then 1 else 0) else (if x<1764 then 1 else (if x<2618 then 1 else 2)))) else (if x<3162 then (if x<2788 then (if x<2740 then 2 else 2) else (if x<3126 then 0 else 2)) else (if x<3276 then (if x<3256 then 0 else 2) else (if x<3284 then 0 else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2259 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1708,1748,1752,1764,1768,2606,2618,2646,2650,2716,2740,2764,2788,2792,2800,3102,3126,3162,3178,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2259 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2259 3288 5
  · have he : independentCachedBranchMembers2259.erase 3288=independentCachedBranchMembers2257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2257
  · have he : independentCachedBranchMembers2259.filter (independentCachedEdge 3288)=independentCachedBranchMembers2258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2258
def independentCachedBranchMembers2260 : Finset ℕ := ([192,252,1614,1650,1748,1752,1764,1768,2606,2740,2788,2792,3126,3162,3178,3244,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2260 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2260 5 (fun x => (if x<2740 then (if x<1748 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<1764 then (if x<1752 then 0 else 1) else (if x<1768 then 1 else (if x<2606 then 0 else 2)))) else (if x<3162 then (if x<2792 then (if x<2788 then 2 else 0) else (if x<3126 then 2 else 2)) else (if x<3244 then (if x<3178 then 1 else 2) else (if x<3276 then 2 else (if x<3312 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2261 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1708,1748,1752,1764,1768,2606,2618,2646,2650,2716,2740,2764,2788,2792,2800,3102,3126,3162,3178,3186,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2261 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2261 3186 5
  · have he : independentCachedBranchMembers2261.erase 3186=independentCachedBranchMembers2259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2259
  · have he : independentCachedBranchMembers2261.filter (independentCachedEdge 3186)=independentCachedBranchMembers2260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2260
def independentCachedBranchMembers2262 : Finset ℕ := ([18,192,1650,1708,1748,1752,2606,2618,2646,2650,2716,2788,2792,2800,3126,3162,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2262 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2262 5 (fun x => (if x<2650 then (if x<1748 then (if x<1650 then (if x<192 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2618 then 2 else (if x<2646 then 0 else 1)))) else (if x<2800 then (if x<2788 then (if x<2716 then 2 else 1) else (if x<2792 then 3 else 0)) else (if x<3162 then (if x<3126 then 1 else 0) else (if x<3300 then 3 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2263 : Finset ℕ := ([18,132,192,252,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2618,2646,2650,2716,2740,2764,2788,2792,2800,3102,3126,3162,3178,3186,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2263 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2263 1692 5
  · have he : independentCachedBranchMembers2263.erase 1692=independentCachedBranchMembers2261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2261
  · have he : independentCachedBranchMembers2263.filter (independentCachedEdge 1692)=independentCachedBranchMembers2262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2262
def independentCachedBranchMembers2264 : Finset ℕ := ([132,252,1594,1650,1752,1768,2716,2788,2800,3126,3162,3178,3244,3256,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2264 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2264 5 (fun x => (if x<2800 then (if x<1752 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1650 then 1 else 2)) else (if x<2716 then (if x<1768 then 1 else 2) else (if x<2788 then 0 else 0))) else (if x<3244 then (if x<3162 then (if x<3126 then 2 else 1) else (if x<3178 then 1 else 3)) else (if x<3284 then (if x<3256 then 0 else 1) else (if x<3300 then 0 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2265 : Finset ℕ := ([252,1768,2788,3126,3162,3256,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2265 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2265 4 (fun x => (if x<3162 then (if x<2788 then (if x<1768 then 0 else 0) else (if x<3126 then 0 else 1)) else (if x<3284 then (if x<3256 then 1 else 1) else (if x<3312 then 1 else 0))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2266 : Finset ℕ := ([132,252,1594,1650,1752,1768,2650,2716,2788,2800,3126,3162,3178,3244,3256,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2266 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2266 2650 4
  · have he : independentCachedBranchMembers2266.erase 2650=independentCachedBranchMembers2264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2264
  · have he : independentCachedBranchMembers2266.filter (independentCachedEdge 2650)=independentCachedBranchMembers2265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2265
def independentCachedBranchMembers2267 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2618,2646,2650,2716,2740,2764,2788,2792,2800,3102,3126,3162,3178,3186,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2267 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2267 1590 5
  · have he : independentCachedBranchMembers2267.erase 1590=independentCachedBranchMembers2263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2263
  · have he : independentCachedBranchMembers2267.filter (independentCachedEdge 1590)=independentCachedBranchMembers2266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2266
def independentCachedBranchMembers2268 : Finset ℕ := ([18,132,1594,1614,1650,1708,1752,1764,2606,2650,2716,2764,2792,2800,3102,3178,3186,3244,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2268 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2268 5 (fun x => (if x<2716 then (if x<1708 then (if x<1594 then (if x<132 then 0 else 0) else (if x<1614 then 0 else (if x<1650 then 1 else 1))) else (if x<1764 then (if x<1752 then 0 else 1) else (if x<2606 then 1 else (if x<2650 then 2 else 0)))) else (if x<3178 then (if x<2792 then (if x<2764 then 2 else 0) else (if x<2800 then 2 else (if x<3102 then 1 else 2))) else (if x<3244 then (if x<3186 then 2 else 0) else (if x<3288 then 2 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2269 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2618,2646,2650,2716,2740,2764,2776,2788,2792,2800,3102,3126,3162,3178,3186,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2269 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2269 2776 5
  · have he : independentCachedBranchMembers2269.erase 2776=independentCachedBranchMembers2267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2267
  · have he : independentCachedBranchMembers2269.filter (independentCachedEdge 2776)=independentCachedBranchMembers2268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2268
def independentCachedBranchMembers2270 : Finset ℕ := ([192,252,1614,1650,1748,1752,1764,1768,2618,2646,2650,2716,2764,2800,3102,3186,3256,3284,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2270 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2270 5 (fun x => (if x<2650 then (if x<1752 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1650 then 1 else (if x<1748 then 1 else 0))) else (if x<1768 then (if x<1764 then 1 else 1) else (if x<2618 then 0 else (if x<2646 then 2 else 2)))) else (if x<3186 then (if x<2764 then (if x<2716 then 1 else 2) else (if x<2800 then 0 else (if x<3102 then 0 else 2))) else (if x<3284 then (if x<3256 then 2 else 2) else (if x<3288 then 2 else (if x<3300 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2271 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3162,3178,3186,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2271 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2271 2674 5
  · have he : independentCachedBranchMembers2271.erase 2674=independentCachedBranchMembers2269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2269
  · have he : independentCachedBranchMembers2271.filter (independentCachedEdge 2674)=independentCachedBranchMembers2270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2270
def independentCachedBranchMembers2272 : Finset ℕ := ([18,132,1614,1650,1748,1752,1764,1768,2618,2646,2650,2716,2764,2800,3126,3162,3178,3244,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2272 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2272 5 (fun x => (if x<2650 then (if x<1752 then (if x<1614 then (if x<132 then 0 else 0) else (if x<1650 then 1 else (if x<1748 then 0 else 1))) else (if x<1768 then (if x<1764 then 2 else 0) else (if x<2618 then 1 else (if x<2646 then 0 else 1)))) else (if x<3162 then (if x<2764 then (if x<2716 then 2 else 2) else (if x<2800 then 1 else (if x<3126 then 1 else 3))) else (if x<3244 then (if x<3178 then 0 else 3) else (if x<3276 then 3 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2273 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3162,3178,3186,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2273 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2273 1776 5
  · have he : independentCachedBranchMembers2273.erase 1776=independentCachedBranchMembers2271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2271
  · have he : independentCachedBranchMembers2273.filter (independentCachedEdge 1776)=independentCachedBranchMembers2272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2272
def independentCachedBranchMembers2274 : Finset ℕ := ([192,252,1594,1614,1650,1708,1752,1764,2606,2650,2716,2764,2792,2800,3126,3162,3256,3276,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2274 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2274 5 (fun x => (if x<2716 then (if x<1708 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1614 then 1 else (if x<1650 then 1 else 2))) else (if x<1764 then (if x<1752 then 1 else 0) else (if x<2606 then 0 else (if x<2650 then 1 else 1)))) else (if x<3162 then (if x<2792 then (if x<2764 then 2 else 0) else (if x<2800 then 3 else (if x<3126 then 0 else 3))) else (if x<3276 then (if x<3256 then 4 else 3) else (if x<3284 then 2 else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2275 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1650,1692,1708,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3162,3178,3186,3244,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2275 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2275 1626 5
  · have he : independentCachedBranchMembers2275.erase 1626=independentCachedBranchMembers2273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2273
  · have he : independentCachedBranchMembers2275.filter (independentCachedEdge 1626)=independentCachedBranchMembers2274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2274
def independentCachedBranchMembers2276 : Finset ℕ := ([18,192,1594,1650,1752,1768,2606,2618,2646,2674,2740,2764,2776,2792,3126,3162,3178,3244,3256,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2276 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2276 5 (fun x => (if x<2764 then (if x<1768 then (if x<1594 then (if x<192 then 0 else 0) else (if x<1650 then 0 else (if x<1752 then 1 else 1))) else (if x<2646 then (if x<2606 then 0 else (if x<2618 then 2 else 3)) else (if x<2674 then 2 else (if x<2740 then 4 else 2)))) else (if x<3178 then (if x<2792 then (if x<2776 then 0 else 3) else (if x<3126 then 4 else (if x<3162 then 0 else 1))) else (if x<3284 then (if x<3244 then 4 else (if x<3256 then 2 else 3)) else (if x<3300 then 2 else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2277 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1650,1692,1708,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2277 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2277 3252 5
  · have he : independentCachedBranchMembers2277.erase 3252=independentCachedBranchMembers2275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2275
  · have he : independentCachedBranchMembers2277.filter (independentCachedEdge 3252)=independentCachedBranchMembers2276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2276
def independentCachedBranchMembers2278 : Finset ℕ := ([1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2646,2650,2740,2764,2800,3102,3162,3178,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2278 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2278 5 (fun x => (if x<2646 then (if x<1708 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1650 then 0 else (if x<1692 then 2 else 0))) else (if x<1764 then (if x<1748 then 1 else (if x<1752 then 2 else 1)) else (if x<1768 then 0 else (if x<2606 then 2 else 1)))) else (if x<3102 then (if x<2740 then (if x<2650 then 2 else 1) else (if x<2764 then 0 else (if x<2800 then 0 else 2))) else (if x<3256 then (if x<3162 then 3 else (if x<3178 then 4 else 3)) else (if x<3276 then 3 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2279 : Finset ℕ := ([1594,1650,1752,1768,2606,2646,2740,2764,3162,3178,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2279 4 (fun x => (if x<2740 then (if x<1768 then (if x<1650 then 0 else (if x<1752 then 1 else 0)) else (if x<2606 then 1 else (if x<2646 then 0 else 1))) else (if x<3178 then (if x<2764 then 2 else (if x<3162 then 0 else 2)) else (if x<3256 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2280 : Finset ℕ := ([1590,1594,1614,1650,1692,1708,1748,1752,1764,1768,2606,2646,2650,2740,2764,2800,3102,3162,3178,3252,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2280 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2280 3252 4
  · have he : independentCachedBranchMembers2280.erase 3252=independentCachedBranchMembers2278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2278
  · have he : independentCachedBranchMembers2280.filter (independentCachedEdge 3252)=independentCachedBranchMembers2279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2279
def independentCachedBranchMembers2281 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1650,1692,1708,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2281 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2281 1740 5
  · have he : independentCachedBranchMembers2281.erase 1740=independentCachedBranchMembers2277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2277
  · have he : independentCachedBranchMembers2281.filter (independentCachedEdge 1740)=independentCachedBranchMembers2280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2280
def independentCachedBranchMembers2282 : Finset ℕ := ([132,1594,1614,1626,1650,1692,1748,1768,2606,2618,2650,2674,2716,2740,2792,3102,3126,3178,3244,3256,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2282 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2282 5 (fun x => (if x<2716 then (if x<1748 then (if x<1626 then (if x<1594 then 0 else (if x<1614 then 0 else 1)) else (if x<1650 then 2 else (if x<1692 then 1 else 0))) else (if x<2618 then (if x<1768 then 1 else (if x<2606 then 1 else 3)) else (if x<2650 then 2 else (if x<2674 then 3 else 0)))) else (if x<3244 then (if x<3102 then (if x<2740 then 3 else (if x<2792 then 2 else 3)) else (if x<3126 then 3 else (if x<3178 then 4 else 0))) else (if x<3288 then (if x<3256 then 3 else (if x<3276 then 4 else 0)) else (if x<3300 then 3 else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2283 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1650,1692,1708,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2283 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2283 3304 5
  · have he : independentCachedBranchMembers2283.erase 3304=independentCachedBranchMembers2281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2281
  · have he : independentCachedBranchMembers2283.filter (independentCachedEdge 3304)=independentCachedBranchMembers2282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2282
def independentCachedBranchMembers2284 : Finset ℕ := ([252,1594,1614,1692,1708,1752,1768,1776,2618,2646,2716,2740,2776,2792,2800,3102,3126,3162,3178,3186,3256,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2284 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2284 5 (fun x => (if x<2776 then (if x<1768 then (if x<1692 then (if x<1594 then 0 else (if x<1614 then 1 else 1)) else (if x<1708 then 0 else (if x<1752 then 1 else 1))) else (if x<2646 then (if x<1776 then 0 else (if x<2618 then 2 else 3)) else (if x<2716 then 3 else (if x<2740 then 3 else 2)))) else (if x<3178 then (if x<3102 then (if x<2792 then 0 else (if x<2800 then 2 else 3)) else (if x<3126 then 3 else (if x<3162 then 4 else 1))) else (if x<3276 then (if x<3186 then 4 else (if x<3256 then 3 else 0)) else (if x<3284 then 0 else (if x<3300 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2285 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1650,1692,1708,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3130,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2285 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2285 3130 5
  · have he : independentCachedBranchMembers2285.erase 3130=independentCachedBranchMembers2283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2283
  · have he : independentCachedBranchMembers2285.filter (independentCachedEdge 3130)=independentCachedBranchMembers2284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2284
def independentCachedBranchMembers2286 : Finset ℕ := ([18,132,192,1594,1614,1692,1708,1752,1768,1776,2606,2650,2674,2764,2788,3102,3126,3162,3178,3186,3256,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2286 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2286 5 (fun x => (if x<2674 then (if x<1708 then (if x<1594 then (if x<132 then 0 else (if x<192 then 0 else 1)) else (if x<1614 then 0 else (if x<1692 then 2 else 2))) else (if x<1776 then (if x<1752 then 0 else (if x<1768 then 1 else 2)) else (if x<2606 then 3 else (if x<2650 then 1 else 0)))) else (if x<3178 then (if x<3102 then (if x<2764 then 3 else (if x<2788 then 0 else 3)) else (if x<3126 then 2 else (if x<3162 then 1 else 4))) else (if x<3276 then (if x<3186 then 2 else (if x<3256 then 0 else 2)) else (if x<3284 then 2 else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2287 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3130,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2287 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2287 1720 5
  · have he : independentCachedBranchMembers2287.erase 1720=independentCachedBranchMembers2285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2285
  · have he : independentCachedBranchMembers2287.filter (independentCachedEdge 1720)=independentCachedBranchMembers2286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2286
def independentCachedBranchMembers2288 : Finset ℕ := ([18,192,252,1594,1614,1650,1748,1768,2646,2764,2788,2800,3102,3126,3178,3244,3256,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2288 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2288 5 (fun x => (if x<2788 then (if x<1650 then (if x<252 then (if x<192 then 0 else 0) else (if x<1594 then 1 else (if x<1614 then 0 else 2))) else (if x<1768 then (if x<1748 then 2 else 1) else (if x<2646 then 0 else (if x<2764 then 2 else 0)))) else (if x<3244 then (if x<3102 then (if x<2800 then 1 else 2) else (if x<3126 then 3 else (if x<3178 then 0 else 3))) else (if x<3288 then (if x<3256 then 3 else (if x<3276 then 4 else 1)) else (if x<3300 then 3 else (if x<3312 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2289 : Finset ℕ := ([18,192,1650,1748,2646,2788,2800,3126,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2289 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2289 4 (fun x => (if x<2788 then (if x<1650 then (if x<192 then 0 else 0) else (if x<1748 then 1 else (if x<2646 then 1 else 1))) else (if x<3126 then (if x<2800 then 0 else 1) else (if x<3300 then 2 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2290 : Finset ℕ := ([18,192,252,1594,1614,1650,1692,1748,1768,2646,2764,2788,2800,3102,3126,3178,3244,3256,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2290 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2290 1692 4
  · have he : independentCachedBranchMembers2290.erase 1692=independentCachedBranchMembers2288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2288
  · have he : independentCachedBranchMembers2290.filter (independentCachedEdge 1692)=independentCachedBranchMembers2289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2289
def independentCachedBranchMembers2291 : Finset ℕ := ([18,1594,1614,1650,2764,2800,3102,3178,3244,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2291 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2291 4 (fun x => (if x<2800 then (if x<1614 then (if x<1594 then 0 else 0) else (if x<1650 then 1 else (if x<2764 then 1 else 0))) else (if x<3244 then (if x<3102 then 1 else (if x<3178 then 2 else 2)) else (if x<3288 then 2 else (if x<3300 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2292 : Finset ℕ := ([18,192,252,1594,1614,1650,1692,1748,1768,2646,2764,2776,2788,2800,3102,3126,3178,3244,3256,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2292 2776 4
  · have he : independentCachedBranchMembers2292.erase 2776=independentCachedBranchMembers2290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2290
  · have he : independentCachedBranchMembers2292.filter (independentCachedEdge 2776)=independentCachedBranchMembers2291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2291
def independentCachedBranchMembers2293 : Finset ℕ := ([192,252,1594,1614,1650,2764,2800,3126,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2293 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2293 4 (fun x => (if x<2764 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1614 then 1 else (if x<1650 then 1 else 2))) else (if x<3256 then (if x<2800 then 0 else (if x<3126 then 0 else 2)) else (if x<3276 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2294 : Finset ℕ := ([18,192,252,1594,1614,1626,1650,1692,1748,1768,2646,2764,2776,2788,2800,3102,3126,3178,3244,3256,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2294 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2294 1626 4
  · have he : independentCachedBranchMembers2294.erase 1626=independentCachedBranchMembers2292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2292
  · have he : independentCachedBranchMembers2294.filter (independentCachedEdge 1626)=independentCachedBranchMembers2293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2293
def independentCachedBranchMembers2295 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2776,2788,2792,2800,3102,3126,3130,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2295 1642 5
  · have he : independentCachedBranchMembers2295.erase 1642=independentCachedBranchMembers2287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2287
  · have he : independentCachedBranchMembers2295.filter (independentCachedEdge 1642)=independentCachedBranchMembers2294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2294
def independentCachedBranchMembers2296 : Finset ℕ := ([18,1590,1614,1626,1650,1708,1748,1768,2606,2618,2646,2716,2740,2764,2776,2788,2800,3102,3126,3162,3186,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2296 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2296 5 (fun x => (if x<2740 then (if x<1748 then (if x<1626 then (if x<1590 then 0 else (if x<1614 then 0 else 1)) else (if x<1650 then 0 else (if x<1708 then 1 else 2))) else (if x<2618 then (if x<1768 then 1 else (if x<2606 then 1 else 2)) else (if x<2646 then 0 else (if x<2716 then 0 else 2)))) else (if x<3126 then (if x<2788 then (if x<2764 then 3 else (if x<2776 then 1 else 3)) else (if x<2800 then 2 else (if x<3102 then 1 else 0))) else (if x<3244 then (if x<3162 then 3 else (if x<3186 then 3 else 0)) else (if x<3256 then 4 else (if x<3284 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2297 : Finset ℕ := ([1614,1626,1650,1748,1768,2606,2618,2716,2740,3102,3126,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2297 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2297 4 (fun x => (if x<2618 then (if x<1748 then (if x<1626 then 0 else (if x<1650 then 1 else 0)) else (if x<1768 then 0 else (if x<2606 then 0 else 2))) else (if x<3102 then (if x<2716 then 1 else (if x<2740 then 2 else 1)) else (if x<3244 then (if x<3126 then 2 else 3) else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2298 : Finset ℕ := ([18,1590,1614,1626,1650,1708,1748,1768,2606,2618,2646,2716,2740,2764,2776,2788,2800,3102,3126,3162,3186,3244,3256,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2298 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2298 3304 4
  · have he : independentCachedBranchMembers2298.erase 3304=independentCachedBranchMembers2296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2296
  · have he : independentCachedBranchMembers2298.filter (independentCachedEdge 3304)=independentCachedBranchMembers2297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2297
def independentCachedBranchMembers2299 : Finset ℕ := ([18,1614,1708,1768,2606,2764,2788,3102,3126,3162,3186,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound2299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2299 4 (fun x => (if x<2788 then (if x<1768 then (if x<1614 then 0 else (if x<1708 then 1 else 0)) else (if x<2606 then 1 else (if x<2764 then 2 else 0))) else (if x<3162 then (if x<3102 then 2 else (if x<3126 then 1 else 3)) else (if x<3256 then (if x<3186 then 3 else 0) else (if x<3284 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2300 : Finset ℕ := ([18,1590,1614,1626,1650,1708,1720,1748,1768,2606,2618,2646,2716,2740,2764,2776,2788,2800,3102,3126,3162,3186,3244,3256,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2300 1720 4
  · have he : independentCachedBranchMembers2300.erase 1720=independentCachedBranchMembers2298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2298
  · have he : independentCachedBranchMembers2300.filter (independentCachedEdge 1720)=independentCachedBranchMembers2299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2299
def independentCachedBranchMembers2301 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2740,2764,2772,2776,2788,2792,2800,3102,3126,3130,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2301 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2301 2772 5
  · have he : independentCachedBranchMembers2301.erase 2772=independentCachedBranchMembers2295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2295
  · have he : independentCachedBranchMembers2301.filter (independentCachedEdge 2772)=independentCachedBranchMembers2300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2300
def independentCachedBranchMembers2302 : Finset ℕ := ([192,1590,1594,1614,1642,1708,1748,1752,1776,2606,2646,2650,2674,2716,2740,2764,2788,2792,3102,3126,3130,3178,3244,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2302 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2302 5 (fun x => (if x<2716 then (if x<1748 then (if x<1614 then (if x<1590 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 1 else (if x<1708 then 2 else 1))) else (if x<2606 then (if x<1752 then 0 else (if x<1776 then 1 else 2)) else (if x<2650 then (if x<2646 then 0 else 3) else (if x<2674 then 1 else 2)))) else (if x<3126 then (if x<2788 then (if x<2740 then 3 else (if x<2764 then 2 else 0)) else (if x<2792 then 3 else (if x<3102 then 2 else 3))) else (if x<3244 then (if x<3130 then 4 else (if x<3178 then 0 else 4)) else (if x<3288 then (if x<3284 then 3 else 3) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2303 : Finset ℕ := ([18,132,192,252,1590,1594,1614,1626,1642,1650,1692,1708,1720,1740,1748,1752,1764,1768,1776,2606,2618,2646,2650,2674,2716,2732,2740,2764,2772,2776,2788,2792,2800,3102,3126,3130,3162,3178,3186,3244,3252,3256,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2303 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2303 2732 5
  · have he : independentCachedBranchMembers2303.erase 2732=independentCachedBranchMembers2301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2301
  · have he : independentCachedBranchMembers2303.filter (independentCachedEdge 2732)=independentCachedBranchMembers2302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2302
end EntropyDesigns.QuadraticRefinement
