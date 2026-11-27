/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch107
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6240 : Finset ℕ := ([1594,1642,1678,1702,1708,1748,2674,2740,2758,3162,3192,3222,3228,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6240 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6240 5 (fun x => (if x<2740 then (if x<1702 then (if x<1642 then 0 else (if x<1678 then 1 else 0)) else (if x<1748 then (if x<1708 then 1 else 2) else (if x<2674 then 2 else 0))) else (if x<3222 then (if x<3162 then (if x<2758 then 1 else 0) else (if x<3192 then 1 else 0)) else (if x<3276 then (if x<3228 then 1 else 2) else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6241 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2668,2674,2730,2740,2758,2776,3126,3132,3150,3162,3174,3192,3222,3228,3242,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6241 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6241 1582 5
  · have he : independentCachedBranchMembers6241.erase 1582=independentCachedBranchMembers6239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6239
  · have he : independentCachedBranchMembers6241.filter (independentCachedEdge 1582)=independentCachedBranchMembers6240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6240
def independentCachedBranchMembers6242 : Finset ℕ := ([1594,1622,1628,1642,1690,1702,1708,1738,2674,2740,2776,3126,3132,3162,3174,3222,3228,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6242 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6242 5 (fun x => (if x<2776 then (if x<1702 then (if x<1628 then (if x<1622 then 0 else 0) else (if x<1642 then 1 else (if x<1690 then 1 else 1))) else (if x<1738 then (if x<1708 then 0 else 1) else (if x<2674 then 0 else (if x<2740 then 2 else 2)))) else (if x<3222 then (if x<3132 then (if x<3126 then 2 else 0) else (if x<3162 then 3 else (if x<3174 then 0 else 3))) else (if x<3242 then (if x<3228 then 3 else 1) else (if x<3276 then 0 else (if x<3312 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6243 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2668,2674,2730,2740,2758,2776,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6243 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6243 2800 5
  · have he : independentCachedBranchMembers6243.erase 2800=independentCachedBranchMembers6241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6241
  · have he : independentCachedBranchMembers6243.filter (independentCachedEdge 2800)=independentCachedBranchMembers6242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6242
def independentCachedBranchMembers6244 : Finset ℕ := ([1582,1594,1628,1652,1708,1720,1738,1762,2668,2740,2758,3132,3150,3162,3174,3222,3242,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6244 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6244 5 (fun x => (if x<2758 then (if x<1720 then (if x<1628 then (if x<1594 then 0 else 1) else (if x<1652 then 0 else (if x<1708 then 1 else 1))) else (if x<1762 then (if x<1738 then 0 else 0) else (if x<2668 then 1 else (if x<2740 then 2 else 2)))) else (if x<3222 then (if x<3150 then (if x<3132 then 2 else 0) else (if x<3162 then 0 else (if x<3174 then 3 else 3))) else (if x<3276 then (if x<3242 then 2 else 0) else (if x<3300 then 3 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6245 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2668,2674,2710,2730,2740,2758,2776,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6245 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6245 2710 5
  · have he : independentCachedBranchMembers6245.erase 2710=independentCachedBranchMembers6243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6243
  · have he : independentCachedBranchMembers6245.filter (independentCachedEdge 2710)=independentCachedBranchMembers6244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6244
def independentCachedBranchMembers6246 : Finset ℕ := ([1582,1652,1678,1714,1720,1748,1762,1768,2674,2740,2776,3126,3132,3162,3174,3222,3228,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6246 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6246 5 (fun x => (if x<2776 then (if x<1748 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1714 then 1 else (if x<1720 then 0 else 1))) else (if x<1768 then (if x<1762 then 1 else 1) else (if x<2674 then 0 else (if x<2740 then 2 else 2)))) else (if x<3222 then (if x<3132 then (if x<3126 then 2 else 0) else (if x<3162 then 3 else (if x<3174 then 2 else 3))) else (if x<3242 then (if x<3228 then 3 else 1) else (if x<3276 then 0 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6247 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2650,2668,2674,2710,2730,2740,2758,2776,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6247 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6247 2650 5
  · have he : independentCachedBranchMembers6247.erase 2650=independentCachedBranchMembers6245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6245
  · have he : independentCachedBranchMembers6247.filter (independentCachedEdge 2650)=independentCachedBranchMembers6246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6246
def independentCachedBranchMembers6248 : Finset ℕ := ([1622,1642,1678,1690,1702,1714,1748,1768,2668,2740,2758,3132,3150,3162,3174,3222,3242,3276,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6248 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6248 5 (fun x => (if x<2758 then (if x<1714 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<1690 then 0 else (if x<1702 then 1 else 1))) else (if x<1768 then (if x<1748 then 0 else 1) else (if x<2668 then 1 else (if x<2740 then 2 else 2)))) else (if x<3222 then (if x<3150 then (if x<3132 then 2 else 2) else (if x<3162 then 0 else (if x<3174 then 3 else 3))) else (if x<3276 then (if x<3242 then 0 else 0) else (if x<3300 then 3 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6249 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2620,2650,2668,2674,2710,2730,2740,2758,2776,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6249 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6249 2620 5
  · have he : independentCachedBranchMembers6249.erase 2620=independentCachedBranchMembers6247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6247
  · have he : independentCachedBranchMembers6249.filter (independentCachedEdge 2620)=independentCachedBranchMembers6248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6248
def independentCachedBranchMembers6250 : Finset ℕ := ([1582,1594,1622,1628,1678,1690,1762,1768,2668,2674,2730,2740,2758,2776,3126,3132,3150,3162,3222,3228,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6250 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6250 5 (fun x => (if x<2740 then (if x<1690 then (if x<1622 then (if x<1594 then 0 else 1) else (if x<1628 then 0 else (if x<1678 then 1 else 1))) else (if x<2668 then (if x<1762 then 0 else (if x<1768 then 0 else 1)) else (if x<2674 then 2 else (if x<2730 then 2 else 0)))) else (if x<3150 then (if x<2776 then (if x<2758 then 2 else 2) else (if x<3126 then 2 else (if x<3132 then 3 else 4))) else (if x<3228 then (if x<3162 then 3 else (if x<3222 then 4 else 4)) else (if x<3300 then 3 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6251 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2620,2650,2668,2674,2710,2730,2740,2758,2776,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6251 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6251 3252 5
  · have he : independentCachedBranchMembers6251.erase 3252=independentCachedBranchMembers6249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6249
  · have he : independentCachedBranchMembers6251.filter (independentCachedEdge 3252)=independentCachedBranchMembers6250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6250
def independentCachedBranchMembers6252 : Finset ℕ := ([1582,1622,1628,1642,1678,1714,1720,1738,2650,2668,2740,2758,2800,3126,3132,3150,3192,3222,3228,3242,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6252 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6252 5 (fun x => (if x<2758 then (if x<1714 then (if x<1628 then (if x<1622 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 1 else 1))) else (if x<2650 then (if x<1720 then 0 else (if x<1738 then 1 else 0)) else (if x<2668 then 2 else (if x<2740 then 2 else 3)))) else (if x<3192 then (if x<3126 then (if x<2800 then 2 else 2) else (if x<3132 then 0 else (if x<3150 then 3 else 0))) else (if x<3242 then (if x<3222 then 1 else (if x<3228 then 3 else 1)) else (if x<3282 then 0 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6253 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2620,2650,2668,2674,2710,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6253 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6253 2788 5
  · have he : independentCachedBranchMembers6253.erase 2788=independentCachedBranchMembers6251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6251
  · have he : independentCachedBranchMembers6253.filter (independentCachedEdge 2788)=independentCachedBranchMembers6252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6252
def independentCachedBranchMembers6254 : Finset ℕ := ([1582,1594,1622,1652,1702,1714,1738,1768,2620,2674,2710,2740,2776,3126,3150,3162,3192,3228,3242,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6254 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6254 5 (fun x => (if x<2740 then (if x<1714 then (if x<1622 then (if x<1594 then 0 else 1) else (if x<1652 then 0 else (if x<1702 then 1 else 1))) else (if x<2620 then (if x<1738 then 0 else (if x<1768 then 0 else 1)) else (if x<2674 then 2 else (if x<2710 then 2 else 2)))) else (if x<3192 then (if x<3126 then (if x<2776 then 3 else 2) else (if x<3150 then 0 else (if x<3162 then 0 else 3))) else (if x<3282 then (if x<3228 then 1 else (if x<3242 then 2 else 0)) else (if x<3300 then 0 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6255 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2620,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6255 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6255 2716 5
  · have he : independentCachedBranchMembers6255.erase 2716=independentCachedBranchMembers6253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6253
  · have he : independentCachedBranchMembers6255.filter (independentCachedEdge 2716)=independentCachedBranchMembers6254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6254
def independentCachedBranchMembers6256 : Finset ℕ := ([1594,1652,1690,1702,1708,1748,1762,1768,2650,2668,2740,2758,2800,3126,3132,3150,3192,3222,3228,3242,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6256 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6256 5 (fun x => (if x<2758 then (if x<1748 then (if x<1690 then (if x<1652 then 0 else 0) else (if x<1702 then 1 else (if x<1708 then 0 else 1))) else (if x<2650 then (if x<1762 then 1 else (if x<1768 then 1 else 0)) else (if x<2668 then 2 else (if x<2740 then 2 else 3)))) else (if x<3192 then (if x<3126 then (if x<2800 then 2 else 2) else (if x<3132 then 0 else (if x<3150 then 3 else 2))) else (if x<3242 then (if x<3222 then 0 else (if x<3228 then 3 else 1)) else (if x<3282 then 0 else (if x<3300 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6257 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6257 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6257 2638 5
  · have he : independentCachedBranchMembers6257.erase 2638=independentCachedBranchMembers6255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6255
  · have he : independentCachedBranchMembers6257.filter (independentCachedEdge 2638)=independentCachedBranchMembers6256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6256
def independentCachedBranchMembers6258 : Finset ℕ := ([1628,1642,1678,1690,1708,1720,1748,1762,2620,2674,2710,2740,2776,3126,3150,3162,3192,3228,3242,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6258 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6258 5 (fun x => (if x<2740 then (if x<1720 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<1690 then 0 else (if x<1708 then 1 else 1))) else (if x<2620 then (if x<1748 then 0 else (if x<1762 then 1 else 1)) else (if x<2674 then 2 else (if x<2710 then 2 else 2)))) else (if x<3192 then (if x<3126 then (if x<2776 then 3 else 2) else (if x<3150 then 2 else (if x<3162 then 0 else 3))) else (if x<3282 then (if x<3228 then 0 else (if x<3242 then 0 else 0)) else (if x<3300 then 1 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6259 : Finset ℕ := ([1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6259 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6259 2614 5
  · have he : independentCachedBranchMembers6259.erase 2614=independentCachedBranchMembers6257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6257
  · have he : independentCachedBranchMembers6259.filter (independentCachedEdge 2614)=independentCachedBranchMembers6258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6258
def independentCachedBranchMembers6260 : Finset ℕ := ([1594,1622,1642,1678,1690,1702,1714,1738,2614,2638,2650,2674,2710,2730,2758,3126,3150,3162,3174,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6260 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6260 5 (fun x => (if x<2674 then (if x<1702 then (if x<1642 then (if x<1622 then 0 else 0) else (if x<1678 then 1 else (if x<1690 then 0 else 1))) else (if x<2614 then (if x<1714 then 1 else (if x<1738 then 2 else 2)) else (if x<2638 then 2 else (if x<2650 then 2 else 1)))) else (if x<3150 then (if x<2730 then (if x<2710 then 0 else 1) else (if x<2758 then 0 else (if x<3126 then 0 else 3))) else (if x<3222 then (if x<3162 then 3 else (if x<3174 then 4 else 4)) else (if x<3242 then 4 else (if x<3282 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6261 : Finset ℕ := ([1594,1642,1678,1702,2650,2674,2710,2758,3162,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6261 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6261 4 (fun x => (if x<2674 then (if x<1678 then (if x<1642 then 0 else 1) else (if x<1702 then 0 else (if x<2650 then 1 else 1))) else (if x<2758 then (if x<2710 then 0 else 1) else (if x<3162 then 0 else (if x<3222 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6262 : Finset ℕ := ([1582,1594,1622,1642,1678,1690,1702,1714,1738,2614,2638,2650,2674,2710,2730,2758,3126,3150,3162,3174,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6262 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6262 1582 4
  · have he : independentCachedBranchMembers6262.erase 1582=independentCachedBranchMembers6260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6260
  · have he : independentCachedBranchMembers6262.filter (independentCachedEdge 1582)=independentCachedBranchMembers6261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6261
def independentCachedBranchMembers6263 : Finset ℕ := ([1642,1702,1714,1738,2614,2638,2650,2710,3126,3150,3162,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6263 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6263 4 (fun x => (if x<2650 then (if x<1738 then (if x<1702 then 0 else (if x<1714 then 0 else 1)) else (if x<2614 then 1 else (if x<2638 then 1 else 1))) else (if x<3150 then (if x<2710 then 0 else (if x<3126 then 0 else 2)) else (if x<3162 then 2 else (if x<3222 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6264 : Finset ℕ := ([1582,1594,1622,1642,1678,1690,1702,1714,1738,1762,2614,2638,2650,2674,2710,2730,2758,3126,3150,3162,3174,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6264 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6264 1762 4
  · have he : independentCachedBranchMembers6264.erase 1762=independentCachedBranchMembers6262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6262
  · have he : independentCachedBranchMembers6264.filter (independentCachedEdge 1762)=independentCachedBranchMembers6263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6263
def independentCachedBranchMembers6265 : Finset ℕ := ([252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6265 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6265 252 5
  · have he : independentCachedBranchMembers6265.erase 252=independentCachedBranchMembers6259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6259
  · have he : independentCachedBranchMembers6265.filter (independentCachedEdge 252)=independentCachedBranchMembers6264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6264
def independentCachedBranchMembers6266 : Finset ℕ := ([1582,1622,1628,1652,1690,1714,1720,1738,1762,1768,2614,2620,2638,2668,2730,2776,2800,3126,3132,3150,3174,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6266 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6266 5 (fun x => (if x<2638 then (if x<1720 then (if x<1652 then (if x<1622 then 0 else (if x<1628 then 0 else 1)) else (if x<1690 then 2 else (if x<1714 then 0 else 2))) else (if x<1768 then (if x<1738 then 1 else (if x<1762 then 1 else 0)) else (if x<2614 then 2 else (if x<2620 then 2 else 1)))) else (if x<3132 then (if x<2776 then (if x<2668 then 1 else (if x<2730 then 2 else 0)) else (if x<2800 then 1 else (if x<3126 then 2 else 3))) else (if x<3242 then (if x<3150 then 4 else (if x<3174 then 3 else 4)) else (if x<3282 then 3 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6267 : Finset ℕ := ([132,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6267 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6267 132 5
  · have he : independentCachedBranchMembers6267.erase 132=independentCachedBranchMembers6265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6265
  · have he : independentCachedBranchMembers6267.filter (independentCachedEdge 132)=independentCachedBranchMembers6266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6266
def independentCachedBranchMembers6268 : Finset ℕ := ([1582,1594,1622,1652,1678,1690,1708,1720,1748,1762,2620,2674,2716,2730,2758,2788,2800,3132,3174,3228,3242,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6268 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6268 5 (fun x => (if x<2716 then (if x<1708 then (if x<1652 then (if x<1594 then 0 else (if x<1622 then 1 else 0)) else (if x<1678 then 1 else (if x<1690 then 2 else 0))) else (if x<1762 then (if x<1720 then 1 else (if x<1748 then 2 else 2)) else (if x<2620 then 0 else (if x<2674 then 1 else 1)))) else (if x<3174 then (if x<2788 then (if x<2730 then 2 else (if x<2758 then 0 else 2)) else (if x<2800 then 1 else (if x<3132 then 2 else 3))) else (if x<3282 then (if x<3228 then 3 else (if x<3242 then 4 else 3)) else (if x<3300 then 4 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6269 : Finset ℕ := ([72,132,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6269 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6269 72 5
  · have he : independentCachedBranchMembers6269.erase 72=independentCachedBranchMembers6267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6267
  · have he : independentCachedBranchMembers6269.filter (independentCachedEdge 72)=independentCachedBranchMembers6268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6268
def independentCachedBranchMembers6270 : Finset ℕ := ([1582,1622,1628,1642,1690,1702,1708,1748,1762,1768,2650,2668,2710,2716,2730,2776,2788,3162,3174,3222,3228,3242,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6270 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6270 5 (fun x => (if x<2710 then (if x<1708 then (if x<1642 then (if x<1622 then 0 else (if x<1628 then 0 else 1)) else (if x<1690 then 1 else (if x<1702 then 0 else 2))) else (if x<1768 then (if x<1748 then 1 else (if x<1762 then 2 else 0)) else (if x<2650 then 2 else (if x<2668 then 1 else 1)))) else (if x<3174 then (if x<2776 then (if x<2716 then 2 else (if x<2730 then 1 else 0)) else (if x<2788 then 2 else (if x<3162 then 2 else 3))) else (if x<3242 then (if x<3222 then 3 else (if x<3228 then 3 else 4)) else (if x<3282 then 3 else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6271 : Finset ℕ := ([48,72,132,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2776,2788,2800,3126,3132,3150,3162,3174,3192,3222,3228,3242,3252,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6271 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6271 48 5
  · have he : independentCachedBranchMembers6271.erase 48=independentCachedBranchMembers6269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6269
  · have he : independentCachedBranchMembers6271.filter (independentCachedEdge 48)=independentCachedBranchMembers6270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6270
end EntropyDesigns.QuadraticRefinement
