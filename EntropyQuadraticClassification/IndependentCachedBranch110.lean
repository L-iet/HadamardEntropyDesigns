/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch109
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6304 : Finset ℕ := ([1594,1678,1748,2788,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6304 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6304 3 (fun x => (if x<1748 then (if x<1678 then 0 else 0) else (if x<2788 then 1 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6305 : Finset ℕ := ([1582,1594,1652,1678,1690,1748,2730,2788,2800,3242,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6305 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6305 1582 3
  · have he : independentCachedBranchMembers6305.erase 1582=independentCachedBranchMembers6303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6303
  · have he : independentCachedBranchMembers6305.filter (independentCachedEdge 1582)=independentCachedBranchMembers6304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6304
def independentCachedBranchMembers6306 : Finset ℕ := ([72,252,1582,1594,1628,1652,1678,1690,1702,1714,1748,1768,2614,2668,2710,2730,2776,2788,2800,3126,3192,3222,3242,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6306 72 4
  · have he : independentCachedBranchMembers6306.erase 72=independentCachedBranchMembers6302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6302
  · have he : independentCachedBranchMembers6306.filter (independentCachedEdge 72)=independentCachedBranchMembers6305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6305
def independentCachedBranchMembers6307 : Finset ℕ := ([48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6307 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6307 66 5
  · have he : independentCachedBranchMembers6307.erase 66=independentCachedBranchMembers6299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6299
  · have he : independentCachedBranchMembers6307.filter (independentCachedEdge 66)=independentCachedBranchMembers6306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6306
def independentCachedBranchMembers6308 : Finset ℕ := ([1594,1622,1628,1642,1678,1714,1720,1748,1762,1768,2638,2674,2710,2716,2730,2758,2800,3150,3192,3222,3228,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6308 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6308 5 (fun x => (if x<2710 then (if x<1720 then (if x<1642 then (if x<1622 then 0 else (if x<1628 then 0 else 1)) else (if x<1678 then 1 else (if x<1714 then 0 else 2))) else (if x<1768 then (if x<1748 then 1 else (if x<1762 then 2 else 0)) else (if x<2638 then 2 else (if x<2674 then 1 else 0)))) else (if x<3192 then (if x<2758 then (if x<2716 then 2 else (if x<2730 then 1 else 0)) else (if x<2800 then 0 else (if x<3150 then 2 else 3))) else (if x<3242 then (if x<3222 then 3 else (if x<3228 then 4 else 3)) else (if x<3276 then 3 else (if x<3312 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6309 : Finset ℕ := ([1622,1628,1714,1720,1762,1768,2638,2730,2800,3150,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6309 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6309 4 (fun x => (if x<2638 then (if x<1720 then (if x<1628 then 0 else (if x<1714 then 1 else 0)) else (if x<1762 then 1 else (if x<1768 then 2 else 3))) else (if x<3150 then (if x<2730 then 0 else (if x<2800 then 0 else 2)) else (if x<3242 then 1 else (if x<3312 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6310 : Finset ℕ := ([132,1594,1622,1628,1642,1678,1714,1720,1748,1762,1768,2638,2674,2710,2716,2730,2758,2800,3150,3192,3222,3228,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6310 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6310 132 4
  · have he : independentCachedBranchMembers6310.erase 132=independentCachedBranchMembers6308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6308
  · have he : independentCachedBranchMembers6310.filter (independentCachedEdge 132)=independentCachedBranchMembers6309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6309
def independentCachedBranchMembers6311 : Finset ℕ := ([1628,1642,1748,1762,1768,2710,2716,2730,3222,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6311 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6311 4 (fun x => (if x<2710 then (if x<1748 then (if x<1642 then 0 else 0) else (if x<1762 then 1 else (if x<1768 then 1 else 2))) else (if x<3222 then (if x<2716 then 2 else (if x<2730 then 0 else 0)) else (if x<3228 then 3 else (if x<3242 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6312 : Finset ℕ := ([1628,1748,1768,2716,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6312 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6312 3 (fun x => (if x<1768 then (if x<1748 then 0 else 1) else (if x<2716 then 0 else (if x<3228 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6313 : Finset ℕ := ([1622,1628,1642,1748,1762,1768,2710,2716,2730,3222,3228,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6313 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6313 1622 3
  · have he : independentCachedBranchMembers6313.erase 1622=independentCachedBranchMembers6311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6311
  · have he : independentCachedBranchMembers6313.filter (independentCachedEdge 1622)=independentCachedBranchMembers6312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6312
def independentCachedBranchMembers6314 : Finset ℕ := ([48,132,1594,1622,1628,1642,1678,1714,1720,1748,1762,1768,2638,2674,2710,2716,2730,2758,2800,3150,3192,3222,3228,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6314 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6314 48 4
  · have he : independentCachedBranchMembers6314.erase 48=independentCachedBranchMembers6310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6310
  · have he : independentCachedBranchMembers6314.filter (independentCachedEdge 48)=independentCachedBranchMembers6313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6313
def independentCachedBranchMembers6315 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6315 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6315 36 5
  · have he : independentCachedBranchMembers6315.erase 36=independentCachedBranchMembers6307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6307
  · have he : independentCachedBranchMembers6315.filter (independentCachedEdge 36)=independentCachedBranchMembers6314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6314
def independentCachedBranchMembers6316 : Finset ℕ := ([1594,1622,1642,1652,1678,1708,1714,1762,2620,2638,2674,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6316 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6316 5 (fun x => (if x<2730 then (if x<1714 then (if x<1652 then (if x<1622 then 0 else (if x<1642 then 0 else 1)) else (if x<1678 then 1 else (if x<1708 then 0 else 1))) else (if x<2638 then (if x<1762 then 1 else (if x<2620 then 0 else 2)) else (if x<2674 then 2 else (if x<2710 then 0 else 2)))) else (if x<3162 then (if x<2776 then (if x<2740 then 0 else (if x<2758 then 1 else 0)) else (if x<2788 then 2 else (if x<3126 then 2 else 3))) else (if x<3228 then (if x<3174 then 3 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 3 else 4) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6317 : Finset ℕ := ([1594,1642,1678,1708,2620,2638,2730,2776,3162,3192,3228,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6317 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6317 4 (fun x => (if x<2730 then (if x<1708 then (if x<1642 then 0 else (if x<1678 then 1 else 0)) else (if x<2620 then 1 else (if x<2638 then 2 else 2))) else (if x<3192 then (if x<2776 then 0 else (if x<3162 then 2 else 1)) else (if x<3228 then 3 else (if x<3276 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6318 : Finset ℕ := ([246,1594,1622,1642,1652,1678,1708,1714,1762,2620,2638,2674,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6318 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6318 246 4
  · have he : independentCachedBranchMembers6318.erase 246=independentCachedBranchMembers6316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6316
  · have he : independentCachedBranchMembers6318.filter (independentCachedEdge 246)=independentCachedBranchMembers6317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6317
def independentCachedBranchMembers6319 : Finset ℕ := ([1622,1652,1714,1762,2620,2638,2730,2776,3126,3174,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6319 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6319 4 (fun x => (if x<2730 then (if x<1762 then (if x<1652 then 0 else (if x<1714 then 1 else 0)) else (if x<2620 then 1 else (if x<2638 then 1 else 0))) else (if x<3174 then (if x<2776 then 0 else (if x<3126 then 2 else 2)) else (if x<3282 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6320 : Finset ℕ := ([132,246,1594,1622,1642,1652,1678,1708,1714,1762,2620,2638,2674,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6320 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6320 132 4
  · have he : independentCachedBranchMembers6320.erase 132=independentCachedBranchMembers6318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6318
  · have he : independentCachedBranchMembers6320.filter (independentCachedEdge 132)=independentCachedBranchMembers6319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6319
def independentCachedBranchMembers6321 : Finset ℕ := ([1594,1652,1678,1714,2710,2730,2776,2788,3126,3192,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6321 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6321 4 (fun x => (if x<2776 then (if x<1714 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<2710 then 1 else (if x<2730 then 1 else 0))) else (if x<3192 then (if x<2788 then 2 else (if x<3126 then 0 else 2)) else (if x<3276 then 2 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6322 : Finset ℕ := ([66,132,246,1594,1622,1642,1652,1678,1708,1714,1762,2620,2638,2674,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6322 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6322 66 4
  · have he : independentCachedBranchMembers6322.erase 66=independentCachedBranchMembers6320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6320
  · have he : independentCachedBranchMembers6322.filter (independentCachedEdge 66)=independentCachedBranchMembers6321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6321
def independentCachedBranchMembers6323 : Finset ℕ := ([1622,1642,1708,1762,2710,2730,2776,2788,3162,3174,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6323 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6323 4 (fun x => (if x<2776 then (if x<1762 then (if x<1642 then 0 else (if x<1708 then 0 else 1)) else (if x<2710 then 1 else (if x<2730 then 0 else 0))) else (if x<3174 then (if x<2788 then 2 else (if x<3162 then 1 else 2)) else (if x<3228 then 2 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6324 : Finset ℕ := ([48,66,132,246,1594,1622,1642,1652,1678,1708,1714,1762,2620,2638,2674,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6324 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6324 48 4
  · have he : independentCachedBranchMembers6324.erase 48=independentCachedBranchMembers6322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6322
  · have he : independentCachedBranchMembers6324.filter (independentCachedEdge 48)=independentCachedBranchMembers6323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6323
def independentCachedBranchMembers6325 : Finset ℕ := ([48,66,132,246,1594,1622,1678,1762,2620,2638,2710,2788,3126,3162,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6325 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6325 4 (fun x => (if x<2620 then (if x<1594 then (if x<132 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1678 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3126 then (if x<2710 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3228 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6326 : Finset ℕ := ([48,66,132,246,1594,1622,1642,1652,1678,1708,1714,1762,2620,2638,2668,2674,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3228,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6326 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6326 2668 4
  · have he : independentCachedBranchMembers6326.erase 2668=independentCachedBranchMembers6324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6324
  · have he : independentCachedBranchMembers6326.filter (independentCachedEdge 2668)=independentCachedBranchMembers6325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6325
def independentCachedBranchMembers6327 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6327 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6327 3288 5
  · have he : independentCachedBranchMembers6327.erase 3288=independentCachedBranchMembers6315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6315
  · have he : independentCachedBranchMembers6327.filter (independentCachedEdge 3288)=independentCachedBranchMembers6326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6326
def independentCachedBranchMembers6328 : Finset ℕ := ([1582,1628,1642,1652,1690,1708,1714,1768,2614,2650,2668,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6328 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6328 5 (fun x => (if x<2730 then (if x<1714 then (if x<1652 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<1690 then 1 else (if x<1708 then 0 else 1))) else (if x<2650 then (if x<1768 then 1 else (if x<2614 then 0 else 2)) else (if x<2668 then 2 else (if x<2716 then 0 else 2)))) else (if x<3150 then (if x<2776 then (if x<2740 then 0 else (if x<2758 then 1 else 2)) else (if x<2800 then 0 else (if x<3132 then 2 else 3))) else (if x<3222 then (if x<3174 then 3 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 3 else 4) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6329 : Finset ℕ := ([1582,1642,1690,1714,2614,2650,2730,2758,3150,3174,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6329 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6329 4 (fun x => (if x<2730 then (if x<1714 then (if x<1642 then 0 else (if x<1690 then 1 else 0)) else (if x<2614 then 1 else (if x<2650 then 2 else 2))) else (if x<3174 then (if x<2758 then 0 else (if x<3150 then 2 else 1)) else (if x<3222 then 3 else (if x<3282 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6330 : Finset ℕ := ([252,1582,1628,1642,1652,1690,1708,1714,1768,2614,2650,2668,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6330 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6330 252 4
  · have he : independentCachedBranchMembers6330.erase 252=independentCachedBranchMembers6328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6328
  · have he : independentCachedBranchMembers6330.filter (independentCachedEdge 252)=independentCachedBranchMembers6329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6329
def independentCachedBranchMembers6331 : Finset ℕ := ([1628,1652,1708,1768,2614,2650,2730,2758,3132,3192,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6331 4 (fun x => (if x<2730 then (if x<1768 then (if x<1652 then 0 else (if x<1708 then 1 else 0)) else (if x<2614 then 1 else (if x<2650 then 1 else 0))) else (if x<3192 then (if x<2758 then 0 else (if x<3132 then 2 else 2)) else (if x<3276 then 3 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6332 : Finset ℕ := ([144,252,1582,1628,1642,1652,1690,1708,1714,1768,2614,2650,2668,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6332 144 4
  · have he : independentCachedBranchMembers6332.erase 144=independentCachedBranchMembers6330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6330
  · have he : independentCachedBranchMembers6332.filter (independentCachedEdge 144)=independentCachedBranchMembers6331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6331
def independentCachedBranchMembers6333 : Finset ℕ := ([1582,1652,1690,1708,2716,2730,2758,2800,3132,3174,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6333 4 (fun x => (if x<2758 then (if x<1708 then (if x<1652 then 0 else (if x<1690 then 0 else 1)) else (if x<2716 then 1 else (if x<2730 then 1 else 0))) else (if x<3174 then (if x<2800 then 2 else (if x<3132 then 0 else 2)) else (if x<3282 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6334 : Finset ℕ := ([72,144,252,1582,1628,1642,1652,1690,1708,1714,1768,2614,2650,2668,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6334 72 4
  · have he : independentCachedBranchMembers6334.erase 72=independentCachedBranchMembers6332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6332
  · have he : independentCachedBranchMembers6334.filter (independentCachedEdge 72)=independentCachedBranchMembers6333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6333
def independentCachedBranchMembers6335 : Finset ℕ := ([1628,1642,1714,1768,2716,2730,2758,2800,3150,3192,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6335 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6335 4 (fun x => (if x<2758 then (if x<1768 then (if x<1642 then 0 else (if x<1714 then 0 else 1)) else (if x<2716 then 1 else (if x<2730 then 0 else 0))) else (if x<3192 then (if x<2800 then 2 else (if x<3150 then 1 else 2)) else (if x<3222 then 2 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
