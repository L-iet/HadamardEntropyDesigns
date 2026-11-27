/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch105
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6176 : Finset ℕ := ([80,130,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3192,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6176 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6176 80 4
  · have he : independentCachedBranchMembers6176.erase 80=independentCachedBranchMembers6174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6174
  · have he : independentCachedBranchMembers6176.filter (independentCachedEdge 80)=independentCachedBranchMembers6175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6175
def independentCachedBranchMembers6177 : Finset ℕ := ([1626,1714,1738,1776,2674,2714,2776,2786,3164,3174,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6177 4 (fun x => (if x<2776 then (if x<1776 then (if x<1714 then 0 else (if x<1738 then 0 else 1)) else (if x<2674 then 1 else (if x<2714 then 0 else 0))) else (if x<3174 then (if x<2786 then 1 else (if x<3164 then 1 else 2)) else (if x<3214 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6178 : Finset ℕ := ([40,80,130,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3192,3214,3242,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6178 40 4
  · have he : independentCachedBranchMembers6178.erase 40=independentCachedBranchMembers6176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6176
  · have he : independentCachedBranchMembers6178.filter (independentCachedEdge 40)=independentCachedBranchMembers6177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6177
def independentCachedBranchMembers6179 : Finset ℕ := ([40,80,130,250,1596,1626,1686,1776,2606,2646,2714,2786,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6179 4 (fun x => (if x<2606 then (if x<1596 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6180 : Finset ℕ := ([40,80,130,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6180 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6180 3276 4
  · have he : independentCachedBranchMembers6180.erase 3276=independentCachedBranchMembers6178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6178
  · have he : independentCachedBranchMembers6180.filter (independentCachedEdge 3276)=independentCachedBranchMembers6179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6179
def independentCachedBranchMembers6181 : Finset ℕ := ([40,80,130,250,1708,1714,1738,1748,2668,2674,2758,2776,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6181 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6181 4 (fun x => (if x<2668 then (if x<1708 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6182 : Finset ℕ := ([40,80,130,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6182 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6182 3102 4
  · have he : independentCachedBranchMembers6182.erase 3102=independentCachedBranchMembers6180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6180
  · have he : independentCachedBranchMembers6182.filter (independentCachedEdge 3102)=independentCachedBranchMembers6181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6181
def independentCachedBranchMembers6183 : Finset ℕ := ([1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786] : List ℕ).toFinset
theorem independentCachedBranchBound6183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6183 4 (fun x => (if x<2606 then (if x<1714 then (if x<1686 then (if x<1626 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<2714 then (if x<2668 then (if x<2646 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2786 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6184 : Finset ℕ := ([40,80,130,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6184 3072 4
  · have he : independentCachedBranchMembers6184.erase 3072=independentCachedBranchMembers6182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6182
  · have he : independentCachedBranchMembers6184.filter (independentCachedEdge 3072)=independentCachedBranchMembers6183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6183
def independentCachedBranchMembers6185 : Finset ℕ := ([40,250,1596,1708,1714,1776,2606,2668,2674,2786,3130,3174,3192,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6185 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6185 4 (fun x => (if x<2674 then (if x<1714 then (if x<1596 then (if x<250 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3192 then (if x<3130 then (if x<2786 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6186 : Finset ℕ := ([40,80,130,222,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6186 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6186 222 4
  · have he : independentCachedBranchMembers6186.erase 222=independentCachedBranchMembers6184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6184
  · have he : independentCachedBranchMembers6186.filter (independentCachedEdge 222)=independentCachedBranchMembers6185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6185
def independentCachedBranchMembers6187 : Finset ℕ := ([80,130,1626,1686,1708,1714,2646,2668,2674,2714,3164,3174,3192,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6187 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6187 4 (fun x => (if x<2674 then (if x<1708 then (if x<1626 then (if x<130 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3192 then (if x<3164 then (if x<2714 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3214 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6188 : Finset ℕ := ([40,80,130,192,222,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6188 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6188 192 4
  · have he : independentCachedBranchMembers6188.erase 192=independentCachedBranchMembers6186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6186
  · have he : independentCachedBranchMembers6188.filter (independentCachedEdge 192)=independentCachedBranchMembers6187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6187
def independentCachedBranchMembers6189 : Finset ℕ := ([80,130,1596,1738,1748,1776,2606,2758,2776,2786,3164,3174,3192,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound6189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6189 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6189 4 (fun x => (if x<2776 then (if x<1748 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1738 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2758 then 1 else 1))) else (if x<3192 then (if x<3164 then (if x<2786 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3242 then (if x<3214 then 3 else 0) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6190 : Finset ℕ := ([18,40,80,130,192,222,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6190 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6190 18 4
  · have he : independentCachedBranchMembers6190.erase 18=independentCachedBranchMembers6188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6188
  · have he : independentCachedBranchMembers6190.filter (independentCachedEdge 18)=independentCachedBranchMembers6189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6189
def independentCachedBranchMembers6191 : Finset ℕ := ([40,250,1626,1686,1738,1748,2646,2714,2758,2776,3130,3174,3192,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6191 4 (fun x => (if x<2758 then (if x<1738 then (if x<1626 then (if x<250 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1748 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3192 then (if x<3130 then (if x<2776 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3252 then (if x<3242 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6192 : Finset ℕ := ([12,18,40,80,130,192,222,250,1596,1626,1686,1708,1714,1738,1748,1776,2606,2646,2668,2674,2714,2758,2776,2786,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6192 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6192 12 4
  · have he : independentCachedBranchMembers6192.erase 12=independentCachedBranchMembers6190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6190
  · have he : independentCachedBranchMembers6192.filter (independentCachedEdge 12)=independentCachedBranchMembers6191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6191
def independentCachedBranchMembers6193 : Finset ℕ := ([12,18,34,40,68,80,130,136,192,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6193 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6193 2662 5
  · have he : independentCachedBranchMembers6193.erase 2662=independentCachedBranchMembers6173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6173
  · have he : independentCachedBranchMembers6193.filter (independentCachedEdge 2662)=independentCachedBranchMembers6192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6192
def independentCachedBranchMembers6194 : Finset ℕ := ([130,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3102,3180,3186,3192,3242,3252,3270,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6194 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6194 5 (fun x => (if x<2652 then (if x<1714 then (if x<1652 then (if x<250 then 0 else (if x<1642 then 0 else 1)) else (if x<1702 then 1 else (if x<1708 then 1 else 2))) else (if x<1748 then (if x<1720 then 0 else (if x<1738 then 1 else 0)) else (if x<2618 then (if x<2606 then 2 else 2) else (if x<2646 then 3 else 2)))) else (if x<3186 then (if x<2786 then (if x<2702 then 3 else (if x<2714 then 3 else 0)) else (if x<3102 then (if x<2792 then 0 else 3) else (if x<3180 then 3 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3242 then 1 else 0)) else (if x<3282 then (if x<3270 then 1 else 4) else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6195 : Finset ℕ := ([1642,1714,1720,1738,2618,2714,2786,2792,3102,3180,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6195 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6195 4 (fun x => (if x<2786 then (if x<1738 then (if x<1714 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2714 then 0 else 1))) else (if x<3180 then (if x<2792 then 0 else (if x<3102 then 1 else 2)) else (if x<3252 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6196 : Finset ℕ := ([80,130,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3102,3180,3186,3192,3242,3252,3270,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6196 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6196 80 4
  · have he : independentCachedBranchMembers6196.erase 80=independentCachedBranchMembers6194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6194
  · have he : independentCachedBranchMembers6196.filter (independentCachedEdge 80)=independentCachedBranchMembers6195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6195
def independentCachedBranchMembers6197 : Finset ℕ := ([1652,1702,1714,1738,2652,2702,2714,2786,3102,3186,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6197 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6197 4 (fun x => (if x<2714 then (if x<1738 then (if x<1702 then 0 else (if x<1714 then 0 else 1)) else (if x<2652 then 1 else (if x<2702 then 0 else 0))) else (if x<3186 then (if x<2786 then 1 else (if x<3102 then 1 else 2)) else (if x<3252 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6198 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3102,3180,3186,3192,3242,3252,3270,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6198 40 4
  · have he : independentCachedBranchMembers6198.erase 40=independentCachedBranchMembers6196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6196
  · have he : independentCachedBranchMembers6198.filter (independentCachedEdge 40)=independentCachedBranchMembers6197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6197
def independentCachedBranchMembers6199 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1720,2606,2646,2714,2786,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6199 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6199 4 (fun x => (if x<2606 then (if x<1642 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3180 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6200 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3102,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6200 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6200 3276 4
  · have he : independentCachedBranchMembers6200.erase 3276=independentCachedBranchMembers6198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6198
  · have he : independentCachedBranchMembers6200.filter (independentCachedEdge 3276)=independentCachedBranchMembers6199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6199
def independentCachedBranchMembers6201 : Finset ℕ := ([40,80,130,250,1708,1714,1738,1748,2618,2652,2702,2792,3180,3186,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6201 4 (fun x => (if x<2618 then (if x<1708 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3180 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3270 then (if x<3186 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6202 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6202 3174 4
  · have he : independentCachedBranchMembers6202.erase 3174=independentCachedBranchMembers6200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6200
  · have he : independentCachedBranchMembers6202.filter (independentCachedEdge 3174)=independentCachedBranchMembers6201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6201
def independentCachedBranchMembers6203 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792] : List ℕ).toFinset
theorem independentCachedBranchBound6203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6203 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6203 4 (fun x => (if x<2606 then (if x<1714 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<2702 then (if x<2646 then (if x<2618 then 2 else 3) else (if x<2652 then 2 else 3)) else (if x<2786 then (if x<2714 then 3 else 2) else (if x<2792 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6204 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6204 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6204 3072 4
  · have he : independentCachedBranchMembers6204.erase 3072=independentCachedBranchMembers6202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6202
  · have he : independentCachedBranchMembers6204.filter (independentCachedEdge 3072)=independentCachedBranchMembers6203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6203
def independentCachedBranchMembers6205 : Finset ℕ := ([80,250,1652,1714,1720,1748,2618,2646,2652,2714,3102,3186,3192,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6205 4 (fun x => (if x<2652 then (if x<1720 then (if x<1652 then (if x<250 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<2618 then (if x<1748 then 2 else 2) else (if x<2646 then 2 else 2))) else (if x<3192 then (if x<3102 then (if x<2714 then 1 else 1) else (if x<3186 then 3 else 0)) else (if x<3282 then (if x<3252 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6206 : Finset ℕ := ([40,80,130,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6206 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6206 238 4
  · have he : independentCachedBranchMembers6206.erase 238=independentCachedBranchMembers6204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6204
  · have he : independentCachedBranchMembers6206.filter (independentCachedEdge 238)=independentCachedBranchMembers6205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6205
def independentCachedBranchMembers6207 : Finset ℕ := ([40,130,1642,1702,1714,1748,2606,2618,2652,2786,3102,3180,3192,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6207 4 (fun x => (if x<2652 then (if x<1714 then (if x<1642 then (if x<130 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2606 then (if x<1748 then 2 else 2) else (if x<2618 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2786 then 2 else 1) else (if x<3180 then 3 else 0)) else (if x<3270 then (if x<3252 then 3 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
