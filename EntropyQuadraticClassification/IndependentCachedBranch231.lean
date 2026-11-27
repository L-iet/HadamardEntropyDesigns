/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch230
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10176 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10176 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10176 3276 4
  · have he : independentCachedBranchMembers10176.erase 3276=independentCachedBranchMembers10174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10174
  · have he : independentCachedBranchMembers10176.filter (independentCachedEdge 3276)=independentCachedBranchMembers10175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10175
def independentCachedBranchMembers10177 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1776,2606,2646,2702,2792,3126,3150,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10177 4 (fun x => (if x<2606 then (if x<1590 then (if x<144 then (if x<72 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1686 then (if x<1614 then 0 else 0) else (if x<1776 then 1 else 1))) else (if x<3126 then (if x<2702 then (if x<2646 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3150 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10178 : Finset ℕ := ([48,72,144,246,1590,1614,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2732,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10178 2732 4
  · have he : independentCachedBranchMembers10178.erase 2732=independentCachedBranchMembers10176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10176
  · have he : independentCachedBranchMembers10178.filter (independentCachedEdge 2732)=independentCachedBranchMembers10177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10177
def independentCachedBranchMembers10179 : Finset ℕ := ([72,144,1590,1740,1746,1776,2606,2762,2772,2792,3150,3180,3186,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10179 4 (fun x => (if x<2772 then (if x<1746 then (if x<1590 then (if x<144 then 0 else 0) else (if x<1740 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2762 then 1 else 1))) else (if x<3186 then (if x<3150 then (if x<2792 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3242 then (if x<3222 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10180 : Finset ℕ := ([48,72,144,246,1590,1614,1650,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2732,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10180 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10180 1650 4
  · have he : independentCachedBranchMembers10180.erase 1650=independentCachedBranchMembers10178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10178
  · have he : independentCachedBranchMembers10180.filter (independentCachedEdge 1650)=independentCachedBranchMembers10179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10179
def independentCachedBranchMembers10181 : Finset ℕ := ([48,246,1614,1686,1740,1746,2646,2702,2762,2772,3126,3180,3186,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10181 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10181 4 (fun x => (if x<2762 then (if x<1740 then (if x<1614 then (if x<246 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1746 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3186 then (if x<3126 then (if x<2772 then 2 else 2) else (if x<3180 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10182 : Finset ℕ := ([48,72,144,246,1590,1614,1644,1650,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2732,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10182 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10182 1644 4
  · have he : independentCachedBranchMembers10182.erase 1644=independentCachedBranchMembers10180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10180
  · have he : independentCachedBranchMembers10182.filter (independentCachedEdge 1644)=independentCachedBranchMembers10181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10181
def independentCachedBranchMembers10183 : Finset ℕ := ([48,144,1614,1706,1716,1776,2606,2666,2676,2702,2762,2772,3150,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10183 4 (fun x => (if x<2676 then (if x<1716 then (if x<1614 then (if x<144 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2666 then 2 else 1))) else (if x<3150 then (if x<2762 then (if x<2702 then 2 else 0) else (if x<2772 then 3 else 3)) else (if x<3252 then (if x<3242 then 1 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10184 : Finset ℕ := ([18,48,72,144,246,1590,1614,1644,1650,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2732,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10184 18 4
  · have he : independentCachedBranchMembers10184.erase 18=independentCachedBranchMembers10182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10182
  · have he : independentCachedBranchMembers10184.filter (independentCachedEdge 18)=independentCachedBranchMembers10183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10183
def independentCachedBranchMembers10185 : Finset ℕ := ([72,246,1590,1686,1706,1716,2646,2666,2676,2762,2772,2792,3126,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound10185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10185 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10185 4 (fun x => (if x<2676 then (if x<1706 then (if x<1590 then (if x<246 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1716 then 2 else 2) else (if x<2666 then 1 else 2))) else (if x<3126 then (if x<2772 then (if x<2762 then 2 else 0) else (if x<2792 then 3 else 3)) else (if x<3242 then (if x<3222 then 1 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10186 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1706,1716,1740,1746,1776,2606,2646,2666,2676,2702,2732,2738,2762,2772,2792,3126,3150,3180,3186,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10186 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10186 12 4
  · have he : independentCachedBranchMembers10186.erase 12=independentCachedBranchMembers10184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10184
  · have he : independentCachedBranchMembers10186.filter (independentCachedEdge 12)=independentCachedBranchMembers10185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10185
def independentCachedBranchMembers10187 : Finset ℕ := ([12,18,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1644,1650,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10187 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10187 2730 5
  · have he : independentCachedBranchMembers10187.erase 2730=independentCachedBranchMembers10167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10167
  · have he : independentCachedBranchMembers10187.filter (independentCachedEdge 2730)=independentCachedBranchMembers10186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10186
def independentCachedBranchMembers10188 : Finset ℕ := ([72,238,1590,1622,1644,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10188 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10188 5 (fun x => (if x<2666 then (if x<1706 then (if x<1622 then (if x<238 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 2 else (if x<1678 then 0 else 1))) else (if x<1748 then (if x<1716 then 3 else (if x<1738 then 2 else 0)) else (if x<2606 then (if x<1776 then 1 else 3) else (if x<2638 then 1 else 0)))) else (if x<3150 then (if x<2764 then (if x<2676 then 4 else (if x<2710 then 1 else 1)) else (if x<2792 then (if x<2770 then 1 else 4) else (if x<3118 then 0 else 3))) else (if x<3222 then (if x<3178 then 2 else (if x<3188 then 0 else 2)) else (if x<3250 then (if x<3244 then 2 else 2) else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10189 : Finset ℕ := ([238,1590,1622,1678,1706,1738,2676,2764,2792,3188,3244,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10189 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10189 4 (fun x => (if x<2676 then (if x<1678 then (if x<1590 then 0 else (if x<1622 then 1 else 2)) else (if x<1706 then 0 else (if x<1738 then 1 else 2))) else (if x<3188 then (if x<2764 then 1 else (if x<2792 then 0 else 1)) else (if x<3244 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10190 : Finset ℕ := ([72,144,238,1590,1622,1644,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10190 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10190 144 4
  · have he : independentCachedBranchMembers10190.erase 144=independentCachedBranchMembers10188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10188
  · have he : independentCachedBranchMembers10190.filter (independentCachedEdge 144)=independentCachedBranchMembers10189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10189
def independentCachedBranchMembers10191 : Finset ℕ := ([72,1590,1678,1716,1738,1776,2638,2676,2764,3150,3188,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10191 4 (fun x => (if x<2638 then (if x<1716 then (if x<1590 then 0 else (if x<1678 then 0 else 1)) else (if x<1738 then 1 else (if x<1776 then 2 else 2))) else (if x<3150 then (if x<2676 then 1 else (if x<2764 then 1 else 0)) else (if x<3188 then 2 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10192 : Finset ℕ := ([40,72,144,238,1590,1622,1644,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10192 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10192 40 4
  · have he : independentCachedBranchMembers10192.erase 40=independentCachedBranchMembers10190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10190
  · have he : independentCachedBranchMembers10192.filter (independentCachedEdge 40)=independentCachedBranchMembers10191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10191
def independentCachedBranchMembers10193 : Finset ℕ := ([238,1590,1678,1706,1716,2638,2666,2676,2764,2770,2792,3118,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10193 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10193 4 (fun x => (if x<2676 then (if x<1706 then (if x<1590 then 0 else (if x<1678 then 1 else 0)) else (if x<2638 then (if x<1716 then 1 else 2) else (if x<2666 then 0 else 2))) else (if x<3118 then (if x<2770 then (if x<2764 then 1 else 3) else (if x<2792 then 3 else 1)) else (if x<3244 then (if x<3222 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10194 : Finset ℕ := ([1678,1706,2676,2770,3118,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10194 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10194 3 (fun x => (if x<2770 then (if x<1706 then 0 else (if x<2676 then 1 else 0)) else (if x<3118 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10195 : Finset ℕ := ([72,238,1590,1678,1706,1716,2638,2666,2676,2764,2770,2792,3118,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10195 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10195 72 3
  · have he : independentCachedBranchMembers10195.erase 72=independentCachedBranchMembers10193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10193
  · have he : independentCachedBranchMembers10195.filter (independentCachedEdge 72)=independentCachedBranchMembers10194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10194
def independentCachedBranchMembers10196 : Finset ℕ := ([40,72,144,238,1590,1622,1644,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10196 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10196 3282 4
  · have he : independentCachedBranchMembers10196.erase 3282=independentCachedBranchMembers10192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10192
  · have he : independentCachedBranchMembers10196.filter (independentCachedEdge 3282)=independentCachedBranchMembers10195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10195
def independentCachedBranchMembers10197 : Finset ℕ := ([144,1622,1706,1716,1776,2606,2666,2676,2710,2764,2770,3150,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10197 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10197 4 (fun x => (if x<2676 then (if x<1716 then (if x<1622 then 0 else (if x<1706 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2666 then 2 else 0))) else (if x<3150 then (if x<2764 then (if x<2710 then 1 else 3) else (if x<2770 then 3 else 1)) else (if x<3250 then (if x<3244 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10198 : Finset ℕ := ([1716,1776,2676,2764,3150,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10198 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10198 3 (fun x => (if x<2764 then (if x<1776 then 0 else (if x<2676 then 1 else 0)) else (if x<3150 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10199 : Finset ℕ := ([40,144,1622,1706,1716,1776,2606,2666,2676,2710,2764,2770,3150,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10199 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10199 40 3
  · have he : independentCachedBranchMembers10199.erase 40=independentCachedBranchMembers10197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10197
  · have he : independentCachedBranchMembers10199.filter (independentCachedEdge 40)=independentCachedBranchMembers10198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10198
def independentCachedBranchMembers10200 : Finset ℕ := ([40,72,144,238,1590,1622,1644,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10200 3276 4
  · have he : independentCachedBranchMembers10200.erase 3276=independentCachedBranchMembers10196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10196
  · have he : independentCachedBranchMembers10200.filter (independentCachedEdge 3276)=independentCachedBranchMembers10199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10199
def independentCachedBranchMembers10201 : Finset ℕ := ([40,238,1622,1678,1738,1748,2638,2710,2764,2770,3118,3178,3188,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10201 4 (fun x => (if x<2764 then (if x<1738 then (if x<1622 then (if x<238 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1748 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3188 then (if x<3118 then (if x<2770 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10202 : Finset ℕ := ([40,72,144,238,1590,1622,1644,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2738,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10202 2738 4
  · have he : independentCachedBranchMembers10202.erase 2738=independentCachedBranchMembers10200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10200
  · have he : independentCachedBranchMembers10202.filter (independentCachedEdge 2738)=independentCachedBranchMembers10201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10201
def independentCachedBranchMembers10203 : Finset ℕ := ([72,144,1590,1738,1748,1776,2606,2764,2770,2792,3150,3178,3188,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10203 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10203 4 (fun x => (if x<2770 then (if x<1748 then (if x<1590 then (if x<144 then 0 else 0) else (if x<1738 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2764 then 1 else 1))) else (if x<3188 then (if x<3150 then (if x<2792 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3244 then (if x<3222 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10204 : Finset ℕ := ([40,72,144,238,1590,1622,1644,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2732,2738,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10204 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10204 2732 4
  · have he : independentCachedBranchMembers10204.erase 2732=independentCachedBranchMembers10202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10202
  · have he : independentCachedBranchMembers10204.filter (independentCachedEdge 2732)=independentCachedBranchMembers10203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10203
def independentCachedBranchMembers10205 : Finset ℕ := ([40,72,144,238,1590,1622,1678,1776,2606,2638,2710,2792,3118,3150,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10205 4 (fun x => (if x<2606 then (if x<1590 then (if x<144 then (if x<72 then 0 else 1) else (if x<238 then 0 else 1)) else (if x<1678 then (if x<1622 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2710 then (if x<2638 then 0 else 1) else (if x<2792 then 0 else 1)) else (if x<3222 then (if x<3150 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10206 : Finset ℕ := ([40,72,144,238,1590,1622,1644,1650,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2732,2738,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10206 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10206 1650 4
  · have he : independentCachedBranchMembers10206.erase 1650=independentCachedBranchMembers10204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10204
  · have he : independentCachedBranchMembers10206.filter (independentCachedEdge 1650)=independentCachedBranchMembers10205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10205
def independentCachedBranchMembers10207 : Finset ℕ := ([238,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,3118,3150,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10207 4 (fun x => (if x<2606 then (if x<1716 then (if x<1678 then 0 else (if x<1706 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 2) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2666 then (if x<2638 then 0 else 3) else (if x<2676 then 1 else 1)) else (if x<3178 then (if x<3150 then 3 else 0) else (if x<3188 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
