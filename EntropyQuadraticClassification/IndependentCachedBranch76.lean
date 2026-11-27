/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch75
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5216 : Finset ℕ := ([40,66,144,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5216 3276 4
  · have he : independentCachedBranchMembers5216.erase 3276=independentCachedBranchMembers5214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5214
  · have he : independentCachedBranchMembers5216.filter (independentCachedEdge 3276)=independentCachedBranchMembers5215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5215
def independentCachedBranchMembers5217 : Finset ℕ := ([40,66,144,250,1708,1714,1734,1752,2668,2674,2762,2772,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5217 4 (fun x => (if x<2668 then (if x<1708 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3130 then (if x<2762 then (if x<2674 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5218 : Finset ℕ := ([40,66,144,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5218 3102 4
  · have he : independentCachedBranchMembers5218.erase 3102=independentCachedBranchMembers5216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5216
  · have he : independentCachedBranchMembers5218.filter (independentCachedEdge 3102)=independentCachedBranchMembers5217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5217
def independentCachedBranchMembers5219 : Finset ℕ := ([1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5219 4 (fun x => (if x<2620 then (if x<1714 then (if x<1686 then (if x<1626 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<2714 then (if x<2668 then (if x<2646 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2772 then (if x<2762 then 2 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5220 : Finset ℕ := ([40,66,144,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5220 3072 4
  · have he : independentCachedBranchMembers5220.erase 3072=independentCachedBranchMembers5218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5218
  · have he : independentCachedBranchMembers5220.filter (independentCachedEdge 3072)=independentCachedBranchMembers5219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5219
def independentCachedBranchMembers5221 : Finset ℕ := ([40,250,1582,1708,1714,1762,2620,2668,2674,2800,3130,3178,3188,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5221 4 (fun x => (if x<2674 then (if x<1714 then (if x<1582 then (if x<250 then 0 else 0) else (if x<1708 then 1 else 2)) else (if x<2620 then (if x<1762 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3188 then (if x<3130 then (if x<2800 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5222 : Finset ℕ := ([40,66,144,222,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5222 222 4
  · have he : independentCachedBranchMembers5222.erase 222=independentCachedBranchMembers5220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5220
  · have he : independentCachedBranchMembers5222.filter (independentCachedEdge 222)=independentCachedBranchMembers5221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5221
def independentCachedBranchMembers5223 : Finset ℕ := ([66,144,1626,1686,1708,1714,2646,2668,2674,2714,3150,3178,3188,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5223 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5223 4 (fun x => (if x<2674 then (if x<1708 then (if x<1626 then (if x<144 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3188 then (if x<3150 then (if x<2714 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5224 : Finset ℕ := ([40,66,144,192,222,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5224 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5224 192 4
  · have he : independentCachedBranchMembers5224.erase 192=independentCachedBranchMembers5222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5222
  · have he : independentCachedBranchMembers5224.filter (independentCachedEdge 192)=independentCachedBranchMembers5223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5223
def independentCachedBranchMembers5225 : Finset ℕ := ([66,144,1582,1734,1752,1762,2620,2762,2772,2800,3150,3178,3188,3228,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound5225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5225 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5225 4 (fun x => (if x<2772 then (if x<1752 then (if x<1582 then (if x<144 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2762 then 1 else 2))) else (if x<3188 then (if x<3150 then (if x<2800 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5226 : Finset ℕ := ([18,40,66,144,192,222,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5226 18 4
  · have he : independentCachedBranchMembers5226.erase 18=independentCachedBranchMembers5224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5224
  · have he : independentCachedBranchMembers5226.filter (independentCachedEdge 18)=independentCachedBranchMembers5225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5225
def independentCachedBranchMembers5227 : Finset ℕ := ([40,250,1626,1686,1734,1752,2646,2714,2762,2772,3130,3178,3188,3238,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5227 4 (fun x => (if x<2762 then (if x<1734 then (if x<1626 then (if x<250 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1752 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3188 then (if x<3130 then (if x<2772 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5228 : Finset ℕ := ([12,18,40,66,144,192,222,250,1582,1626,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2714,2762,2772,2800,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5228 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5228 12 4
  · have he : independentCachedBranchMembers5228.erase 12=independentCachedBranchMembers5226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5226
  · have he : independentCachedBranchMembers5228.filter (independentCachedEdge 12)=independentCachedBranchMembers5227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5227
def independentCachedBranchMembers5229 : Finset ℕ := ([12,18,34,40,66,72,132,144,192,222,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1734,1740,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5229 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5229 1702 5
  · have he : independentCachedBranchMembers5229.erase 1702=independentCachedBranchMembers5209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5209
  · have he : independentCachedBranchMembers5229.filter (independentCachedEdge 1702)=independentCachedBranchMembers5228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5228
def independentCachedBranchMembers5230 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5230 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5230 2676 6
  · have he : independentCachedBranchMembers5230.erase 2676=independentCachedBranchMembers4968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4968
  · have he : independentCachedBranchMembers5230.filter (independentCachedEdge 2676)=independentCachedBranchMembers5229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5229
def independentCachedBranchMembers5231 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2618,2638,2662,2668,2674,2680,2716,2730,2740,2762,2772,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5231 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5231 6 (fun x => (if x<2762 then (if x<2638 then (if x<1714 then (if x<1652 then 0 else (if x<1708 then 0 else 0)) else (if x<1752 then (if x<1734 then 0 else 0) else (if x<2618 then 0 else 1))) else (if x<2680 then (if x<2668 then (if x<2662 then 1 else 2) else (if x<2674 then 3 else 3)) else (if x<2730 then (if x<2716 then 2 else 1) else (if x<2740 then 2 else 2)))) else (if x<3214 then (if x<3132 then (if x<2792 then (if x<2772 then 3 else 3) else (if x<3126 then 1 else 4)) else (if x<3164 then (if x<3158 then 5 else 5) else (if x<3178 then 4 else 1))) else (if x<3276 then (if x<3238 then (if x<3226 then 4 else 5) else (if x<3256 then 2 else 1)) else (if x<3300 then (if x<3282 then 1 else 3) else (if x<3312 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5232 : Finset ℕ := ([1652,1708,1752,2662,2674,2716,2730,2762,2792,3126,3158,3214,3226,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5232 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5232 5 (fun x => (if x<2762 then (if x<2662 then (if x<1708 then 0 else (if x<1752 then 0 else 0)) else (if x<2716 then (if x<2674 then 1 else 2) else (if x<2730 then 3 else 1))) else (if x<3214 then (if x<3126 then (if x<2792 then 2 else 3) else (if x<3158 then 2 else 1)) else (if x<3256 then (if x<3226 then 2 else 1) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5233 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2618,2638,2662,2668,2674,2680,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5233 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5233 2786 5
  · have he : independentCachedBranchMembers5233.erase 2786=independentCachedBranchMembers5231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5231
  · have he : independentCachedBranchMembers5233.filter (independentCachedEdge 2786)=independentCachedBranchMembers5232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5232
def independentCachedBranchMembers5234 : Finset ℕ := ([1652,1708,1752,2668,2680,2716,2740,2772,2792,3132,3164,3256,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5234 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5234 5 (fun x => (if x<2772 then (if x<2668 then (if x<1708 then 0 else (if x<1752 then 0 else 0)) else (if x<2716 then (if x<2680 then 1 else 2) else (if x<2740 then 1 else 2))) else (if x<3256 then (if x<3132 then (if x<2792 then 3 else 3) else (if x<3164 then 1 else 4)) else (if x<3300 then (if x<3276 then 2 else 1) else (if x<3312 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5235 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2618,2638,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5235 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5235 2710 5
  · have he : independentCachedBranchMembers5235.erase 2710=independentCachedBranchMembers5233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5233
  · have he : independentCachedBranchMembers5235.filter (independentCachedEdge 2710)=independentCachedBranchMembers5234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5234
def independentCachedBranchMembers5236 : Finset ℕ := ([1652,1714,1734,2618,2638,2674,2680,2740,2762,3126,3132,3214,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5236 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5236 5 (fun x => (if x<2740 then (if x<2618 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2674 then (if x<2638 then 1 else 1) else (if x<2680 then 2 else 3))) else (if x<3214 then (if x<3126 then (if x<2762 then 2 else 3) else (if x<3132 then 2 else 3)) else (if x<3276 then (if x<3256 then 3 else 1) else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5237 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5237 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5237 2650 5
  · have he : independentCachedBranchMembers5237.erase 2650=independentCachedBranchMembers5235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5235
  · have he : independentCachedBranchMembers5237.filter (independentCachedEdge 2650)=independentCachedBranchMembers5236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5236
def independentCachedBranchMembers5238 : Finset ℕ := ([1652,1714,1734,2618,2638,2662,2668,2730,2772,3158,3164,3226,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5238 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5238 5 (fun x => (if x<2730 then (if x<2618 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2662 then (if x<2638 then 1 else 1) else (if x<2668 then 2 else 3))) else (if x<3226 then (if x<3158 then (if x<2772 then 2 else 3) else (if x<3164 then 2 else 3)) else (if x<3276 then (if x<3256 then 2 else 1) else (if x<3300 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5239 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5239 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5239 2606 5
  · have he : independentCachedBranchMembers5239.erase 2606=independentCachedBranchMembers5237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5237
  · have he : independentCachedBranchMembers5239.filter (independentCachedEdge 2606)=independentCachedBranchMembers5238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5238
def independentCachedBranchMembers5240 : Finset ℕ := ([1652,1714,1752,2618,2650,2662,2668,2710,2716,2730,2762,3126,3132,3158,3164,3178,3226,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5240 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5240 5 (fun x => (if x<2762 then (if x<2662 then (if x<1752 then (if x<1714 then 0 else 0) else (if x<2618 then 0 else (if x<2650 then 1 else 2))) else (if x<2710 then (if x<2668 then 1 else 2) else (if x<2716 then 1 else (if x<2730 then 2 else 2)))) else (if x<3178 then (if x<3132 then (if x<3126 then 1 else 0) else (if x<3158 then 3 else (if x<3164 then 3 else 0))) else (if x<3238 then (if x<3226 then 1 else 0) else (if x<3276 then 3 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5241 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5241 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5241 1776 5
  · have he : independentCachedBranchMembers5241.erase 1776=independentCachedBranchMembers5239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5239
  · have he : independentCachedBranchMembers5241.filter (independentCachedEdge 1776)=independentCachedBranchMembers5240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5240
def independentCachedBranchMembers5242 : Finset ℕ := ([1652,1714,1752,2606,2638,2674,2680,2740,2772,2786,2792,3126,3132,3158,3164,3178,3226,3238,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5242 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5242 5 (fun x => (if x<2792 then (if x<2674 then (if x<1752 then (if x<1714 then 0 else 0) else (if x<2606 then 0 else (if x<2638 then 1 else 2))) else (if x<2740 then (if x<2680 then 1 else 2) else (if x<2772 then 1 else (if x<2786 then 2 else 2)))) else (if x<3178 then (if x<3132 then (if x<3126 then 1 else 0) else (if x<3158 then 3 else (if x<3164 then 3 else 0))) else (if x<3238 then (if x<3226 then 1 else 0) else (if x<3276 then 3 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5243 : Finset ℕ := ([1642,1652,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5243 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5243 1690 5
  · have he : independentCachedBranchMembers5243.erase 1690=independentCachedBranchMembers5241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5241
  · have he : independentCachedBranchMembers5243.filter (independentCachedEdge 1690)=independentCachedBranchMembers5242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5242
def independentCachedBranchMembers5244 : Finset ℕ := ([1652,1708,1734,2606,2618,2668,2680,2716,2740,2762,2786,3132,3158,3178,3214,3226,3238,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5244 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5244 5 (fun x => (if x<2786 then (if x<2668 then (if x<1734 then (if x<1708 then 0 else 0) else (if x<2606 then 0 else (if x<2618 then 1 else 2))) else (if x<2716 then (if x<2680 then 2 else 1) else (if x<2740 then 1 else (if x<2762 then 2 else 1)))) else (if x<3226 then (if x<3158 then (if x<3132 then 2 else 0) else (if x<3178 then 0 else (if x<3214 then 1 else 0))) else (if x<3276 then (if x<3238 then 3 else 3) else (if x<3300 then 3 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5245 : Finset ℕ := ([1622,1642,1652,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5245 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5245 1622 5
  · have he : independentCachedBranchMembers5245.erase 1622=independentCachedBranchMembers5243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5243
  · have he : independentCachedBranchMembers5245.filter (independentCachedEdge 1622)=independentCachedBranchMembers5244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5244
def independentCachedBranchMembers5246 : Finset ℕ := ([1652,1708,1734,2638,2650,2662,2674,2710,2730,2772,2792,3132,3158,3178,3214,3226,3238,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5246 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5246 5 (fun x => (if x<2792 then (if x<2662 then (if x<1734 then (if x<1708 then 0 else 0) else (if x<2638 then 0 else (if x<2650 then 1 else 2))) else (if x<2710 then (if x<2674 then 2 else 1) else (if x<2730 then 1 else (if x<2772 then 1 else 2)))) else (if x<3226 then (if x<3158 then (if x<3132 then 2 else 0) else (if x<3178 then 0 else (if x<3214 then 1 else 0))) else (if x<3276 then (if x<3238 then 3 else 3) else (if x<3300 then 3 else (if x<3312 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5247 : Finset ℕ := ([1596,1622,1642,1652,1690,1708,1714,1734,1752,1776,2606,2618,2638,2650,2662,2668,2674,2680,2710,2716,2730,2740,2762,2772,2786,2792,3126,3132,3158,3164,3178,3214,3226,3238,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5247 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5247 1596 5
  · have he : independentCachedBranchMembers5247.erase 1596=independentCachedBranchMembers5245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5245
  · have he : independentCachedBranchMembers5247.filter (independentCachedEdge 1596)=independentCachedBranchMembers5246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5246
end EntropyDesigns.QuadraticRefinement
