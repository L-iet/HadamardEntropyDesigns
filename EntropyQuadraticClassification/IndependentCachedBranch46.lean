/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch45
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4256 : Finset ℕ := ([36,40,1596,1644,1652,1720,1768,2668,2680,2732,2740,3132,3192,3244,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4256 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4256 5 (fun x => (if x<2668 then (if x<1644 then (if x<40 then 0 else (if x<1596 then 1 else 0)) else (if x<1720 then (if x<1652 then 1 else 2) else (if x<1768 then 1 else 2))) else (if x<3132 then (if x<2732 then (if x<2680 then 0 else 1) else (if x<2740 then 1 else 0)) else (if x<3244 then (if x<3192 then 1 else 2) else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4257 : Finset ℕ := ([36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3192,3222,3226,3244,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4257 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4257 222 5
  · have he : independentCachedBranchMembers4257.erase 222=independentCachedBranchMembers4255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4255
  · have he : independentCachedBranchMembers4257.filter (independentCachedEdge 222)=independentCachedBranchMembers4256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4256
def independentCachedBranchMembers4258 : Finset ℕ := ([66,130,1596,1652,1678,1720,1734,2680,2740,2758,2762,3132,3150,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4258 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4258 5 (fun x => (if x<2680 then (if x<1652 then (if x<130 then 0 else (if x<1596 then 1 else 0)) else (if x<1720 then (if x<1678 then 1 else 2) else (if x<1734 then 2 else 1))) else (if x<3132 then (if x<2758 then (if x<2740 then 1 else 0) else (if x<2762 then 0 else 1)) else (if x<3192 then (if x<3150 then 1 else 2) else (if x<3274 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4259 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3192,3222,3226,3244,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4259 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4259 18 5
  · have he : independentCachedBranchMembers4259.erase 18=independentCachedBranchMembers4257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4257
  · have he : independentCachedBranchMembers4259.filter (independentCachedEdge 18)=independentCachedBranchMembers4258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4258
def independentCachedBranchMembers4260 : Finset ℕ := ([18,36,1626,1644,1652,1734,1768,2668,2714,2732,2740,2758,3132,3150,3158,3192,3222,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4260 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4260 5 (fun x => (if x<2740 then (if x<1734 then (if x<1626 then (if x<36 then 0 else 0) else (if x<1644 then 0 else (if x<1652 then 0 else 1))) else (if x<2668 then (if x<1768 then 1 else 1) else (if x<2714 then 2 else (if x<2732 then 0 else 0)))) else (if x<3192 then (if x<3132 then (if x<2758 then 2 else 2) else (if x<3150 then 2 else (if x<3158 then 2 else 1))) else (if x<3274 then (if x<3222 then 1 else 2) else (if x<3282 then 1 else (if x<3300 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4261 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3192,3222,3226,3244,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4261 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4261 3270 5
  · have he : independentCachedBranchMembers4261.erase 3270=independentCachedBranchMembers4259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4259
  · have he : independentCachedBranchMembers4261.filter (independentCachedEdge 3270)=independentCachedBranchMembers4260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4260
def independentCachedBranchMembers4262 : Finset ℕ := ([18,40,66,222,1626,1652,1686,1720,1734,1746,1768,2732,2758,2770,3132,3158,3192,3226,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4262 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4262 5 (fun x => (if x<1768 then (if x<1652 then (if x<66 then (if x<40 then 0 else 0) else (if x<222 then 1 else (if x<1626 then 1 else 1))) else (if x<1720 then (if x<1686 then 2 else 0) else (if x<1734 then 2 else (if x<1746 then 1 else 2)))) else (if x<3158 then (if x<2758 then (if x<2732 then 3 else 3) else (if x<2770 then 4 else (if x<3132 then 0 else 2))) else (if x<3226 then (if x<3192 then 0 else 4) else (if x<3274 then 2 else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4263 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3188,3192,3222,3226,3244,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4263 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4263 3188 5
  · have he : independentCachedBranchMembers4263.erase 3188=independentCachedBranchMembers4261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4261
  · have he : independentCachedBranchMembers4263.filter (independentCachedEdge 3188)=independentCachedBranchMembers4262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4262
def independentCachedBranchMembers4264 : Finset ℕ := ([18,222,1596,1626,1678,1686,1768,2668,2680,2732,2740,2758,2762,2770,3132,3150,3158,3222,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4264 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4264 5 (fun x => (if x<2740 then (if x<1686 then (if x<1596 then (if x<222 then 0 else 0) else (if x<1626 then 1 else (if x<1678 then 0 else 1))) else (if x<2668 then (if x<1768 then 0 else 1) else (if x<2680 then 2 else (if x<2732 then 1 else 1)))) else (if x<3150 then (if x<2762 then (if x<2758 then 2 else 2) else (if x<2770 then 1 else (if x<3132 then 0 else 2))) else (if x<3222 then (if x<3158 then 2 else 0) else (if x<3226 then 2 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4265 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3188,3192,3222,3226,3244,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4265 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4265 2620 5
  · have he : independentCachedBranchMembers4265.erase 2620=independentCachedBranchMembers4263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4263
  · have he : independentCachedBranchMembers4265.filter (independentCachedEdge 2620)=independentCachedBranchMembers4264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4264
def independentCachedBranchMembers4266 : Finset ℕ := ([18,36,130,222,1626,1644,1652,1678,1686,1720,1746,2668,2762,2770,3132,3150,3158,3192,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound4266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4266 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4266 5 (fun x => (if x<1746 then (if x<1644 then (if x<130 then (if x<36 then 0 else 0) else (if x<222 then 1 else (if x<1626 then 1 else 0))) else (if x<1678 then (if x<1652 then 0 else 2) else (if x<1686 then 1 else (if x<1720 then 2 else 2)))) else (if x<3150 then (if x<2762 then (if x<2668 then 1 else 3) else (if x<2770 then 1 else (if x<3132 then 0 else 3))) else (if x<3226 then (if x<3158 then 3 else (if x<3192 then 2 else 2)) else (if x<3244 then 0 else (if x<3270 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4267 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3188,3192,3222,3226,3244,3256,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4267 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4267 3256 5
  · have he : independentCachedBranchMembers4267.erase 3256=independentCachedBranchMembers4265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4265
  · have he : independentCachedBranchMembers4267.filter (independentCachedEdge 3256)=independentCachedBranchMembers4266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4266
def independentCachedBranchMembers4268 : Finset ℕ := ([66,222,1626,1644,1678,1720,1734,2646,2668,2740,2758,2762,3132,3150,3188,3192,3222,3226,3244,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4268 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4268 5 (fun x => (if x<2758 then (if x<1720 then (if x<1626 then (if x<222 then 0 else 0) else (if x<1644 then 0 else (if x<1678 then 1 else 1))) else (if x<2646 then (if x<1734 then 1 else 0) else (if x<2668 then 0 else (if x<2740 then 2 else 2)))) else (if x<3192 then (if x<3132 then (if x<2762 then 2 else 0) else (if x<3150 then 2 else (if x<3188 then 0 else 3))) else (if x<3244 then (if x<3222 then 1 else (if x<3226 then 2 else 1)) else (if x<3282 then 1 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4269 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3180,3188,3192,3222,3226,3244,3256,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4269 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4269 3180 5
  · have he : independentCachedBranchMembers4269.erase 3180=independentCachedBranchMembers4267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4267
  · have he : independentCachedBranchMembers4269.filter (independentCachedEdge 3180)=independentCachedBranchMembers4268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4268
def independentCachedBranchMembers4270 : Finset ℕ := ([40,130,1596,1626,1644,1652,1678,1686,1720,1734,1768,2620,2668,2758,3150,3158,3192,3226,3244,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4270 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4270 5 (fun x => (if x<2620 then (if x<1652 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1626 then 0 else (if x<1644 then 1 else 1))) else (if x<1720 then (if x<1678 then 2 else (if x<1686 then 1 else 0)) else (if x<1734 then 1 else (if x<1768 then 2 else 2)))) else (if x<3192 then (if x<2758 then (if x<2668 then 3 else 0) else (if x<3150 then 0 else (if x<3158 then 1 else 2))) else (if x<3274 then (if x<3226 then 0 else (if x<3244 then 1 else 1)) else (if x<3282 then 2 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4271 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3162,3180,3188,3192,3222,3226,3244,3256,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4271 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4271 3162 5
  · have he : independentCachedBranchMembers4271.erase 3162=independentCachedBranchMembers4269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4269
  · have he : independentCachedBranchMembers4271.filter (independentCachedEdge 3162)=independentCachedBranchMembers4270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4270
def independentCachedBranchMembers4272 : Finset ℕ := ([18,40,1596,1626,1652,1678,1734,1746,1768,2646,2668,2680,2732,2762,3158,3180,3192,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4272 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4272 5 (fun x => (if x<2680 then (if x<1678 then (if x<1596 then (if x<40 then 0 else 0) else (if x<1626 then 1 else (if x<1652 then 1 else 2))) else (if x<1768 then (if x<1734 then 1 else (if x<1746 then 2 else 0)) else (if x<2646 then 0 else (if x<2668 then 0 else 0)))) else (if x<3192 then (if x<2762 then (if x<2732 then 1 else 1) else (if x<3158 then 1 else (if x<3180 then 2 else 3))) else (if x<3256 then (if x<3222 then 2 else (if x<3244 then 0 else 0)) else (if x<3274 then 3 else (if x<3300 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4273 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1720,1734,1738,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3162,3180,3188,3192,3222,3226,3244,3256,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4273 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4273 1738 5
  · have he : independentCachedBranchMembers4273.erase 1738=independentCachedBranchMembers4271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4271
  · have he : independentCachedBranchMembers4273.filter (independentCachedEdge 1738)=independentCachedBranchMembers4272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4272
def independentCachedBranchMembers4274 : Finset ℕ := ([130,222,1596,1626,1644,1678,1720,1746,1768,2680,2714,2732,2758,2762,3150,3188,3192,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4274 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4274 5 (fun x => (if x<2732 then (if x<1678 then (if x<1596 then (if x<222 then 0 else 0) else (if x<1626 then 1 else (if x<1644 then 1 else 2))) else (if x<1768 then (if x<1720 then 0 else (if x<1746 then 2 else 0)) else (if x<2680 then 1 else (if x<2714 then 1 else 0)))) else (if x<3192 then (if x<2762 then (if x<2758 then 1 else 0) else (if x<3150 then 1 else (if x<3188 then 2 else 3))) else (if x<3244 then (if x<3222 then 2 else (if x<3226 then 0 else 2)) else (if x<3270 then 2 else (if x<3274 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4275 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3162,3180,3188,3192,3222,3226,3244,3256,3270,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4275 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4275 1708 5
  · have he : independentCachedBranchMembers4275.erase 1708=independentCachedBranchMembers4273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4273
  · have he : independentCachedBranchMembers4275.filter (independentCachedEdge 1708)=independentCachedBranchMembers4274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4274
def independentCachedBranchMembers4276 : Finset ℕ := ([36,66,130,222,1596,1626,1652,1678,1734,1746,1768,2620,2714,2740,2758,2770,3158,3180,3192,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4276 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4276 5 (fun x => (if x<2714 then (if x<1652 then (if x<222 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1596 then 1 else (if x<1626 then 0 else 0))) else (if x<1746 then (if x<1678 then 2 else (if x<1734 then 1 else 2)) else (if x<1768 then 1 else (if x<2620 then 2 else 3)))) else (if x<3192 then (if x<2770 then (if x<2740 then 1 else (if x<2758 then 0 else 1)) else (if x<3158 then 0 else (if x<3180 then 2 else 3))) else (if x<3256 then (if x<3222 then 2 else (if x<3244 then 1 else 0)) else (if x<3274 then 3 else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4277 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3162,3180,3188,3192,3222,3226,3244,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4277 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4277 3304 5
  · have he : independentCachedBranchMembers4277.erase 3304=independentCachedBranchMembers4275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4275
  · have he : independentCachedBranchMembers4277.filter (independentCachedEdge 3304)=independentCachedBranchMembers4276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4276
def independentCachedBranchMembers4278 : Finset ℕ := ([36,40,66,1596,1626,1644,1678,1720,1746,1768,2620,2646,2668,2740,2770,3150,3188,3192,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4278 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4278 5 (fun x => (if x<2646 then (if x<1644 then (if x<66 then (if x<40 then 0 else 1) else (if x<1596 then 0 else (if x<1626 then 0 else 0))) else (if x<1746 then (if x<1678 then 1 else (if x<1720 then 2 else 1)) else (if x<1768 then 2 else (if x<2620 then 2 else 1)))) else (if x<3192 then (if x<2770 then (if x<2668 then 3 else (if x<2740 then 3 else 0)) else (if x<3150 then 0 else (if x<3188 then 3 else 3))) else (if x<3244 then (if x<3222 then 1 else (if x<3226 then 2 else 4)) else (if x<3270 then 0 else (if x<3274 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4279 : Finset ℕ := ([66,1596,1678,1720,2620,2740,3150,3188,3192,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4279 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4279 4 (fun x => (if x<2740 then (if x<1678 then (if x<1596 then 0 else 0) else (if x<1720 then 1 else (if x<2620 then 1 else 2))) else (if x<3192 then (if x<3150 then 0 else (if x<3188 then 1 else 2)) else (if x<3270 then 1 else (if x<3274 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4280 : Finset ℕ := ([18,36,40,66,1596,1626,1644,1678,1720,1746,1768,2620,2646,2668,2740,2770,3150,3188,3192,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4280 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4280 18 4
  · have he : independentCachedBranchMembers4280.erase 18=independentCachedBranchMembers4278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4278
  · have he : independentCachedBranchMembers4280.filter (independentCachedEdge 18)=independentCachedBranchMembers4279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4279
def independentCachedBranchMembers4281 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4281 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4281 3214 5
  · have he : independentCachedBranchMembers4281.erase 3214=independentCachedBranchMembers4277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4277
  · have he : independentCachedBranchMembers4281.filter (independentCachedEdge 3214)=independentCachedBranchMembers4280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4280
def independentCachedBranchMembers4282 : Finset ℕ := ([18,40,130,222,1644,1678,1734,1746,1768,2646,2668,2680,2714,2740,2758,2770,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4282 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4282 5 (fun x => (if x<2714 then (if x<1734 then (if x<222 then (if x<40 then 0 else (if x<130 then 0 else 1)) else (if x<1644 then 1 else (if x<1678 then 0 else 1))) else (if x<2646 then (if x<1746 then 2 else (if x<1768 then 1 else 2)) else (if x<2668 then 2 else (if x<2680 then 3 else 2)))) else (if x<3162 then (if x<2770 then (if x<2740 then 1 else (if x<2758 then 3 else 1)) else (if x<3132 then 0 else (if x<3150 then 3 else 3))) else (if x<3244 then (if x<3188 then 4 else (if x<3222 then 4 else 0)) else (if x<3274 then (if x<3256 then 0 else 2) else (if x<3300 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4283 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4283 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4283 3252 5
  · have he : independentCachedBranchMembers4283.erase 3252=independentCachedBranchMembers4281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4281
  · have he : independentCachedBranchMembers4283.filter (independentCachedEdge 3252)=independentCachedBranchMembers4282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4282
def independentCachedBranchMembers4284 : Finset ℕ := ([18,36,40,66,130,222,1626,1644,1686,1708,1734,1738,2680,2740,2770,3132,3158,3162,3180,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4284 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4284 5 (fun x => (if x<2680 then (if x<1626 then (if x<66 then (if x<36 then 0 else (if x<40 then 0 else 1)) else (if x<130 then 1 else (if x<222 then 2 else 2))) else (if x<1708 then (if x<1644 then 0 else (if x<1686 then 0 else 2)) else (if x<1734 then 1 else (if x<1738 then 1 else 2)))) else (if x<3180 then (if x<3132 then (if x<2740 then 3 else (if x<2770 then 3 else 0)) else (if x<3158 then 1 else (if x<3162 then 1 else 3))) else (if x<3244 then (if x<3222 then 4 else (if x<3226 then 3 else 0)) else (if x<3270 then 0 else (if x<3274 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4285 : Finset ℕ := ([18,222,1644,1708,1734,1738,3132,3158,3162,3222,3226] : List ℕ).toFinset
theorem independentCachedBranchBound4285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4285 4 (fun x => (if x<1738 then (if x<1644 then (if x<222 then 0 else 0) else (if x<1708 then 1 else (if x<1734 then 2 else 1))) else (if x<3162 then (if x<3132 then 2 else (if x<3158 then 1 else 0)) else (if x<3222 then 2 else (if x<3226 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4286 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1686,1708,1734,1738,2680,2740,2770,3132,3158,3162,3180,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4286 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4286 1596 4
  · have he : independentCachedBranchMembers4286.erase 1596=independentCachedBranchMembers4284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4284
  · have he : independentCachedBranchMembers4286.filter (independentCachedEdge 1596)=independentCachedBranchMembers4285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4285
def independentCachedBranchMembers4287 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,2800,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4287 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4287 2800 5
  · have he : independentCachedBranchMembers4287.erase 2800=independentCachedBranchMembers4283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4283
  · have he : independentCachedBranchMembers4287.filter (independentCachedEdge 2800)=independentCachedBranchMembers4286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4286
end EntropyDesigns.QuadraticRefinement
