/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch106
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6208 : Finset ℕ := ([40,80,130,136,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6208 136 4
  · have he : independentCachedBranchMembers6208.erase 136=independentCachedBranchMembers6206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6206
  · have he : independentCachedBranchMembers6208.filter (independentCachedEdge 136)=independentCachedBranchMembers6207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6207
def independentCachedBranchMembers6209 : Finset ℕ := ([80,250,1642,1702,1708,1738,2606,2702,2786,2792,3102,3186,3192,3252,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6209 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6209 4 (fun x => (if x<2786 then (if x<1708 then (if x<1642 then (if x<250 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2606 then (if x<1738 then 2 else 2) else (if x<2702 then 1 else 2))) else (if x<3192 then (if x<3102 then (if x<2792 then 1 else 2) else (if x<3186 then 3 else 0)) else (if x<3282 then (if x<3252 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6210 : Finset ℕ := ([40,68,80,130,136,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6210 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6210 68 4
  · have he : independentCachedBranchMembers6210.erase 68=independentCachedBranchMembers6208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6208
  · have he : independentCachedBranchMembers6210.filter (independentCachedEdge 68)=independentCachedBranchMembers6209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6209
def independentCachedBranchMembers6211 : Finset ℕ := ([40,130,1652,1708,1720,1738,2646,2702,2714,2792,3102,3180,3192,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6211 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6211 4 (fun x => (if x<2714 then (if x<1720 then (if x<1652 then (if x<130 then 0 else 0) else (if x<1708 then 1 else 1)) else (if x<2646 then (if x<1738 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3192 then (if x<3102 then (if x<2792 then 2 else 2) else (if x<3180 then 3 else 0)) else (if x<3270 then (if x<3252 then 3 else 3) else (if x<3282 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6212 : Finset ℕ := ([34,40,68,80,130,136,238,250,1642,1652,1702,1708,1714,1720,1738,1748,2606,2618,2646,2652,2702,2714,2786,2792,3072,3102,3174,3180,3186,3192,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6212 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6212 34 4
  · have he : independentCachedBranchMembers6212.erase 34=independentCachedBranchMembers6210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6210
  · have he : independentCachedBranchMembers6212.filter (independentCachedEdge 34)=independentCachedBranchMembers6211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6211
def independentCachedBranchMembers6213 : Finset ℕ := ([12,18,34,40,68,80,130,136,192,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2590,2606,2618,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6213 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6213 2590 5
  · have he : independentCachedBranchMembers6213.erase 2590=independentCachedBranchMembers6193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6193
  · have he : independentCachedBranchMembers6213.filter (independentCachedEdge 2590)=independentCachedBranchMembers6212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6212
def independentCachedBranchMembers6214 : Finset ℕ := ([1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1776,3072,3118,3130,3158,3164,3180,3186,3192,3214,3226,3242,3252,3270,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6214 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6214 5 (fun x => (if x<3158 then (if x<1720 then (if x<1686 then (if x<1642 then 0 else (if x<1652 then 1 else 0)) else (if x<1708 then (if x<1702 then 0 else 1) else (if x<1714 then 2 else 2))) else (if x<1776 then (if x<1738 then 0 else (if x<1748 then 2 else 2)) else (if x<3118 then (if x<3072 then 1 else 3) else (if x<3130 then 1 else 3)))) else (if x<3242 then (if x<3186 then (if x<3164 then 0 else (if x<3180 then 3 else 4)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3226 then 3 else 0))) else (if x<3282 then (if x<3252 then 2 else (if x<3270 then 0 else 4)) else (if x<3298 then (if x<3288 then 2 else 4) else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6215 : Finset ℕ := ([1652,1708,1720,1738,3072,3158,3186,3214,3226,3242,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6215 4 (fun x => (if x<3186 then (if x<1738 then (if x<1708 then 0 else (if x<1720 then 0 else 1)) else (if x<3072 then 1 else (if x<3158 then 2 else 0))) else (if x<3242 then (if x<3214 then 2 else (if x<3226 then 0 else 1)) else (if x<3288 then 2 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6216 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1776,3072,3118,3130,3158,3164,3180,3186,3192,3214,3226,3242,3252,3270,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6216 1596 4
  · have he : independentCachedBranchMembers6216.erase 1596=independentCachedBranchMembers6214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6214
  · have he : independentCachedBranchMembers6216.filter (independentCachedEdge 1596)=independentCachedBranchMembers6215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6215
def independentCachedBranchMembers6217 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1720,1776,3130,3164,3180,3186,3214,3270,3288,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6217 4 (fun x => (if x<3130 then (if x<1686 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3214 then (if x<3180 then (if x<3164 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6218 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1776,3072,3118,3130,3158,3164,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6218 3276 4
  · have he : independentCachedBranchMembers6218.erase 3276=independentCachedBranchMembers6216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6216
  · have he : independentCachedBranchMembers6218.filter (independentCachedEdge 3276)=independentCachedBranchMembers6217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6217
def independentCachedBranchMembers6219 : Finset ℕ := ([1596,1626,1686,1708,1714,1738,1748,1776,3118,3158,3180,3186,3226,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6219 4 (fun x => (if x<3118 then (if x<1714 then (if x<1686 then (if x<1626 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3226 then (if x<3180 then (if x<3158 then 2 else 2) else (if x<3186 then 3 else 3)) else (if x<3288 then (if x<3270 then 2 else 3) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6220 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1776,3072,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6220 3174 4
  · have he : independentCachedBranchMembers6220.erase 3174=independentCachedBranchMembers6218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6218
  · have he : independentCachedBranchMembers6220.filter (independentCachedEdge 3174)=independentCachedBranchMembers6219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6219
def independentCachedBranchMembers6221 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1738,1748,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6221 4 (fun x => (if x<3118 then (if x<1714 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3214 then (if x<3158 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)) else (if x<3298 then (if x<3226 then 3 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6222 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1776,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6222 3102 4
  · have he : independentCachedBranchMembers6222.erase 3102=independentCachedBranchMembers6220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6220
  · have he : independentCachedBranchMembers6222.filter (independentCachedEdge 3102)=independentCachedBranchMembers6221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6221
def independentCachedBranchMembers6223 : Finset ℕ := ([1652,1702,1708,1748,1776,3072,3118,3158,3164,3186,3192,3214,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6223 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6223 4 (fun x => (if x<3158 then (if x<1748 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<3072 then (if x<1776 then 1 else 2) else (if x<3118 then 3 else 1))) else (if x<3214 then (if x<3186 then (if x<3164 then 1 else 0) else (if x<3192 then 2 else 3)) else (if x<3282 then (if x<3242 then 0 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6224 : Finset ℕ := ([1702,1708,3072,3118,3214,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6224 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6224 3 (fun x => (if x<3118 then (if x<1708 then 0 else (if x<3072 then 1 else 2)) else (if x<3214 then 0 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6225 : Finset ℕ := ([1626,1652,1702,1708,1748,1776,3072,3118,3158,3164,3186,3192,3214,3242,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6225 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6225 1626 3
  · have he : independentCachedBranchMembers6225.erase 1626=independentCachedBranchMembers6223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6223
  · have he : independentCachedBranchMembers6225.filter (independentCachedEdge 1626)=independentCachedBranchMembers6224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6224
def independentCachedBranchMembers6226 : Finset ℕ := ([1596,1626,1642,1652,1686,1702,1708,1714,1720,1738,1748,1764,1776,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6226 1764 4
  · have he : independentCachedBranchMembers6226.erase 1764=independentCachedBranchMembers6222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6222
  · have he : independentCachedBranchMembers6226.filter (independentCachedEdge 1764)=independentCachedBranchMembers6225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6225
def independentCachedBranchMembers6227 : Finset ℕ := ([1642,1686,1708,1720,1748,3072,3118,3130,3158,3180,3192,3242,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6227 4 (fun x => (if x<3130 then (if x<1720 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<3072 then (if x<1748 then 1 else 2) else (if x<3118 then 3 else 0))) else (if x<3242 then (if x<3180 then (if x<3158 then 2 else 1) else (if x<3192 then 3 else 1)) else (if x<3282 then (if x<3270 then 3 else 3) else (if x<3304 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6228 : Finset ℕ := ([1708,1720,3072,3158,3242,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6228 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6228 3 (fun x => (if x<3158 then (if x<1720 then 0 else (if x<3072 then 1 else 2)) else (if x<3242 then 0 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6229 : Finset ℕ := ([1596,1642,1686,1708,1720,1748,3072,3118,3130,3158,3180,3192,3242,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6229 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6229 1596 3
  · have he : independentCachedBranchMembers6229.erase 1596=independentCachedBranchMembers6227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6227
  · have he : independentCachedBranchMembers6229.filter (independentCachedEdge 1596)=independentCachedBranchMembers6228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6228
def independentCachedBranchMembers6230 : Finset ℕ := ([1596,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6230 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6230 1692 4
  · have he : independentCachedBranchMembers6230.erase 1692=independentCachedBranchMembers6226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6226
  · have he : independentCachedBranchMembers6230.filter (independentCachedEdge 1692)=independentCachedBranchMembers6229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6229
def independentCachedBranchMembers6231 : Finset ℕ := ([1626,1642,1714,1720,1738,1776,3072,3130,3186,3192,3226,3242,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6231 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6231 4 (fun x => (if x<3186 then (if x<1738 then (if x<1714 then (if x<1642 then 0 else 1) else (if x<1720 then 0 else 1)) else (if x<3072 then (if x<1776 then 2 else 2) else (if x<3130 then 3 else 0))) else (if x<3282 then (if x<3226 then (if x<3192 then 3 else 1) else (if x<3242 then 3 else 1)) else (if x<3298 then (if x<3288 then 0 else 2) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6232 : Finset ℕ := ([1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6232 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6232 1614 4
  · have he : independentCachedBranchMembers6232.erase 1614=independentCachedBranchMembers6230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6230
  · have he : independentCachedBranchMembers6232.filter (independentCachedEdge 1614)=independentCachedBranchMembers6231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6231
def independentCachedBranchMembers6233 : Finset ℕ := ([1596,1652,1686,1702,1714,1738,3072,3164,3180,3192,3214,3226,3242,3270,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6233 4 (fun x => (if x<3180 then (if x<1714 then (if x<1686 then (if x<1652 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<3072 then (if x<1738 then 2 else 2) else (if x<3164 then 3 else 1))) else (if x<3242 then (if x<3214 then (if x<3192 then 0 else 3) else (if x<3226 then 1 else 2)) else (if x<3282 then (if x<3270 then 3 else 0) else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6234 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6234 1590 4
  · have he : independentCachedBranchMembers6234.erase 1590=independentCachedBranchMembers6232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6232
  · have he : independentCachedBranchMembers6234.filter (independentCachedEdge 1590)=independentCachedBranchMembers6233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6233
def independentCachedBranchMembers6235 : Finset ℕ := ([12,18,34,40,68,80,130,136,192,222,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2560,2590,2606,2618,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2758,2764,2770,2776,2786,2792,3072,3102,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6235 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6235 2560 5
  · have he : independentCachedBranchMembers6235.erase 2560=independentCachedBranchMembers6213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6213
  · have he : independentCachedBranchMembers6235.filter (independentCachedEdge 2560)=independentCachedBranchMembers6234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6234
def independentCachedBranchMembers6236 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6236 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6236 1716 6
  · have he : independentCachedBranchMembers6236.erase 1716=independentCachedBranchMembers5892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5892
  · have he : independentCachedBranchMembers6236.filter (independentCachedEdge 1716)=independentCachedBranchMembers6235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6235
def independentCachedBranchMembers6237 : Finset ℕ := ([1594,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2668,2674,2730,2740,2758,2776,3126,3132,3150,3162,3174,3192,3222,3228,3242,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6237 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6237 6 (fun x => (if x<2730 then (if x<1714 then (if x<1678 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1702 then (if x<1690 then 0 else 2) else (if x<1708 then 1 else 2))) else (if x<1762 then (if x<1738 then (if x<1720 then 3 else 1) else (if x<1748 then 3 else 2)) else (if x<2668 then (if x<1768 then 2 else 0) else (if x<2674 then 4 else 4)))) else (if x<3174 then (if x<3126 then (if x<2758 then (if x<2740 then 0 else 1) else (if x<2776 then 4 else 4)) else (if x<3150 then (if x<3132 then 3 else 5) else (if x<3162 then 3 else 5))) else (if x<3242 then (if x<3222 then (if x<3192 then 4 else 4) else (if x<3228 then 5 else 2)) else (if x<3282 then (if x<3276 then 2 else 4) else (if x<3300 then 2 else (if x<3312 then 2 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6238 : Finset ℕ := ([1628,1652,1708,1720,1748,1768,2668,2740,2776,3132,3192,3228,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6238 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6238 5 (fun x => (if x<2740 then (if x<1720 then (if x<1652 then 0 else (if x<1708 then 1 else 0)) else (if x<1768 then (if x<1748 then 1 else 2) else (if x<2668 then 2 else 0))) else (if x<3228 then (if x<3132 then (if x<2776 then 1 else 2) else (if x<3192 then 0 else 3)) else (if x<3300 then (if x<3276 then 3 else 0) else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6239 : Finset ℕ := ([1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2668,2674,2730,2740,2758,2776,3126,3132,3150,3162,3174,3192,3222,3228,3242,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6239 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6239 1622 5
  · have he : independentCachedBranchMembers6239.erase 1622=independentCachedBranchMembers6237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6237
  · have he : independentCachedBranchMembers6239.filter (independentCachedEdge 1622)=independentCachedBranchMembers6238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6238
end EntropyDesigns.QuadraticRefinement
