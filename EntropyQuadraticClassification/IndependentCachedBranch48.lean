/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch47
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4320 : Finset ℕ := ([40,66,1626,1644,1678,1686,1720,1738,1746,1764,2646,2680,2714,2732,2740,2758,2800,3132,3150,3192,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4320 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4320 2800 4
  · have he : independentCachedBranchMembers4320.erase 2800=independentCachedBranchMembers4318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4318
  · have he : independentCachedBranchMembers4320.filter (independentCachedEdge 2800)=independentCachedBranchMembers4319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4319
def independentCachedBranchMembers4321 : Finset ℕ := ([1626,1678,1686,1764,2680,2732,2740,2758,3132,3150,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4321 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4321 4 (fun x => (if x<2740 then (if x<1764 then (if x<1678 then 0 else (if x<1686 then 0 else 1)) else (if x<2680 then 1 else (if x<2732 then 0 else 0))) else (if x<3150 then (if x<2758 then 1 else (if x<3132 then 1 else 2)) else (if x<3226 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4322 : Finset ℕ := ([40,66,1626,1644,1678,1686,1720,1738,1746,1764,2620,2646,2680,2714,2732,2740,2758,2800,3132,3150,3192,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4322 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4322 2620 4
  · have he : independentCachedBranchMembers4322.erase 2620=independentCachedBranchMembers4320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4320
  · have he : independentCachedBranchMembers4322.filter (independentCachedEdge 2620)=independentCachedBranchMembers4321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4321
def independentCachedBranchMembers4323 : Finset ℕ := ([40,66,1644,1678,1738,1764,2732,2758,3150,3244,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4323 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4323 4 (fun x => (if x<2732 then (if x<1678 then (if x<66 then 0 else (if x<1644 then 0 else 1)) else (if x<1738 then 1 else (if x<1764 then 2 else 2))) else (if x<3244 then (if x<2758 then 0 else (if x<3150 then 0 else 1)) else (if x<3270 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4324 : Finset ℕ := ([40,66,1626,1644,1652,1678,1686,1720,1738,1746,1764,2620,2646,2680,2714,2732,2740,2758,2800,3132,3150,3192,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4324 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4324 1652 4
  · have he : independentCachedBranchMembers4324.erase 1652=independentCachedBranchMembers4322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4322
  · have he : independentCachedBranchMembers4324.filter (independentCachedEdge 1652)=independentCachedBranchMembers4323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4323
def independentCachedBranchMembers4325 : Finset ℕ := ([1644,1678,1738,1764,2646,2680,2714,2740,2800,3150,3244,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4325 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4325 4 (fun x => (if x<2714 then (if x<1764 then (if x<1678 then 0 else (if x<1738 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 2 else 0))) else (if x<3150 then (if x<2740 then 0 else (if x<2800 then 1 else 2)) else (if x<3270 then (if x<3244 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4326 : Finset ℕ := ([1678,1764,2680,2740,3150,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4326 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4326 3 (fun x => (if x<2740 then (if x<1764 then 0 else (if x<2680 then 0 else 1)) else (if x<3150 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4327 : Finset ℕ := ([1644,1678,1738,1764,2620,2646,2680,2714,2740,2800,3150,3244,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4327 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4327 2620 3
  · have he : independentCachedBranchMembers4327.erase 2620=independentCachedBranchMembers4325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4325
  · have he : independentCachedBranchMembers4327.filter (independentCachedEdge 2620)=independentCachedBranchMembers4326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4326
def independentCachedBranchMembers4328 : Finset ℕ := ([40,66,1626,1644,1652,1678,1686,1720,1738,1746,1764,2620,2646,2680,2714,2732,2740,2758,2800,3132,3150,3158,3192,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4328 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4328 3158 4
  · have he : independentCachedBranchMembers4328.erase 3158=independentCachedBranchMembers4324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4324
  · have he : independentCachedBranchMembers4328.filter (independentCachedEdge 3158)=independentCachedBranchMembers4327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4327
def independentCachedBranchMembers4329 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,2620,2646,2650,2668,2680,2710,2714,2732,2740,2758,2762,2770,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4329 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4329 1690 5
  · have he : independentCachedBranchMembers4329.erase 1690=independentCachedBranchMembers4317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4317
  · have he : independentCachedBranchMembers4329.filter (independentCachedEdge 1690)=independentCachedBranchMembers4328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4328
def independentCachedBranchMembers4330 : Finset ℕ := ([36,130,1614,1626,1652,1686,1708,1734,1746,1768,2620,2646,2668,2680,2714,2740,2762,2800,3132,3158,3180,3192,3214,3252,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4330 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4330 5 (fun x => (if x<2680 then (if x<1708 then (if x<1626 then (if x<130 then 0 else (if x<1614 then 0 else 1)) else (if x<1652 then 2 else (if x<1686 then 0 else 1))) else (if x<1768 then (if x<1734 then 1 else (if x<1746 then 2 else 0)) else (if x<2646 then (if x<2620 then 2 else 0) else (if x<2668 then 1 else 1)))) else (if x<3158 then (if x<2762 then (if x<2714 then 2 else (if x<2740 then 0 else 1)) else (if x<2800 then 2 else (if x<3132 then 3 else 4))) else (if x<3214 then (if x<3180 then 4 else (if x<3192 then 0 else 3)) else (if x<3274 then (if x<3252 then 4 else 3) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4331 : Finset ℕ := ([36,130,1614,1708,1734,1768,2668,2762,3180,3214,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4331 4 (fun x => (if x<2668 then (if x<1708 then (if x<130 then 0 else (if x<1614 then 0 else 1)) else (if x<1734 then 1 else (if x<1768 then 2 else 2))) else (if x<3214 then (if x<2762 then 0 else (if x<3180 then 0 else 1)) else (if x<3274 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4332 : Finset ℕ := ([36,130,1614,1626,1652,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2714,2740,2762,2800,3132,3158,3180,3192,3214,3252,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4332 1720 4
  · have he : independentCachedBranchMembers4332.erase 1720=independentCachedBranchMembers4330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4330
  · have he : independentCachedBranchMembers4332.filter (independentCachedEdge 1720)=independentCachedBranchMembers4331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4331
def independentCachedBranchMembers4333 : Finset ℕ := ([1614,1708,1734,1768,2646,2680,2714,2740,2800,3180,3214,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4333 4 (fun x => (if x<2714 then (if x<1768 then (if x<1708 then 0 else (if x<1734 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 0 else 1))) else (if x<3180 then (if x<2740 then 2 else (if x<2800 then 0 else 2)) else (if x<3274 then (if x<3214 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4334 : Finset ℕ := ([1614,1768,2680,2740,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4334 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4334 3 (fun x => (if x<2740 then (if x<1768 then 0 else (if x<2680 then 0 else 1)) else (if x<3214 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4335 : Finset ℕ := ([1614,1708,1734,1768,2620,2646,2680,2714,2740,2800,3180,3214,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4335 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4335 2620 3
  · have he : independentCachedBranchMembers4335.erase 2620=independentCachedBranchMembers4333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4333
  · have he : independentCachedBranchMembers4335.filter (independentCachedEdge 2620)=independentCachedBranchMembers4334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4334
def independentCachedBranchMembers4336 : Finset ℕ := ([36,130,1614,1626,1652,1686,1708,1720,1734,1746,1768,2620,2646,2668,2680,2714,2740,2762,2800,3132,3158,3180,3192,3214,3226,3252,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4336 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4336 3226 4
  · have he : independentCachedBranchMembers4336.erase 3226=independentCachedBranchMembers4332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4332
  · have he : independentCachedBranchMembers4336.filter (independentCachedEdge 3226)=independentCachedBranchMembers4335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4335
def independentCachedBranchMembers4337 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,2620,2646,2650,2668,2680,2710,2714,2732,2740,2758,2762,2770,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4337 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4337 1622 5
  · have he : independentCachedBranchMembers4337.erase 1622=independentCachedBranchMembers4329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4329
  · have he : independentCachedBranchMembers4337.filter (independentCachedEdge 1622)=independentCachedBranchMembers4336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4336
def independentCachedBranchMembers4338 : Finset ℕ := ([36,66,130,222,1596,1626,1652,1678,1734,1746,1768,2646,2668,2680,2710,2732,2762,2800,3132,3150,3162,3188,3214,3226,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4338 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4338 5 (fun x => (if x<2710 then (if x<1678 then (if x<222 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1626 then (if x<1596 then 1 else 0) else (if x<1652 then 0 else 2))) else (if x<1768 then (if x<1734 then 1 else (if x<1746 then 2 else 1)) else (if x<2668 then (if x<2646 then 2 else 2) else (if x<2680 then 3 else 2)))) else (if x<3188 then (if x<2800 then (if x<2732 then 1 else (if x<2762 then 0 else 0)) else (if x<3150 then (if x<3132 then 3 else 4) else (if x<3162 then 3 else 4))) else (if x<3252 then (if x<3214 then 3 else (if x<3226 then 4 else 1)) else (if x<3282 then (if x<3270 then 0 else 1) else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4339 : Finset ℕ := ([36,130,1626,1678,1734,2680,2710,2732,3132,3150,3188,3226,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4339 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4339 4 (fun x => (if x<2732 then (if x<1678 then (if x<130 then 0 else (if x<1626 then 0 else 1)) else (if x<2680 then (if x<1734 then 1 else 2) else (if x<2710 then 1 else 2))) else (if x<3188 then (if x<3132 then 1 else (if x<3150 then 0 else 3)) else (if x<3282 then (if x<3226 then 3 else 0) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4340 : Finset ℕ := ([36,66,130,222,1596,1614,1626,1652,1678,1734,1746,1768,2646,2668,2680,2710,2732,2762,2800,3132,3150,3162,3188,3214,3226,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4340 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4340 1614 4
  · have he : independentCachedBranchMembers4340.erase 1614=independentCachedBranchMembers4338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4338
  · have he : independentCachedBranchMembers4340.filter (independentCachedEdge 1614)=independentCachedBranchMembers4339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4339
def independentCachedBranchMembers4341 : Finset ℕ := ([1626,1652,1678,1746,2646,2680,2732,2800,3132,3150,3226,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4341 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4341 4 (fun x => (if x<2800 then (if x<1746 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<2680 then (if x<2646 then 1 else 0) else (if x<2732 then 0 else 1))) else (if x<3226 then (if x<3132 then 1 else (if x<3150 then 2 else 2)) else (if x<3270 then (if x<3252 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4342 : Finset ℕ := ([1652,1678,2680,2800,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4342 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4342 3 (fun x => (if x<2800 then (if x<1678 then 0 else (if x<2680 then 1 else 0)) else (if x<3226 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4343 : Finset ℕ := ([66,1626,1652,1678,1746,2646,2680,2732,2800,3132,3150,3226,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4343 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4343 66 3
  · have he : independentCachedBranchMembers4343.erase 66=independentCachedBranchMembers4341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4341
  · have he : independentCachedBranchMembers4343.filter (independentCachedEdge 66)=independentCachedBranchMembers4342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4342
def independentCachedBranchMembers4344 : Finset ℕ := ([36,66,130,222,1596,1614,1626,1652,1678,1690,1734,1746,1768,2646,2668,2680,2710,2732,2762,2800,3132,3150,3162,3188,3214,3226,3252,3270,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4344 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4344 1690 4
  · have he : independentCachedBranchMembers4344.erase 1690=independentCachedBranchMembers4340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4340
  · have he : independentCachedBranchMembers4344.filter (independentCachedEdge 1690)=independentCachedBranchMembers4343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4343
def independentCachedBranchMembers4345 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,2620,2646,2650,2668,2680,2710,2714,2732,2740,2758,2762,2770,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4345 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4345 2792 5
  · have he : independentCachedBranchMembers4345.erase 2792=independentCachedBranchMembers4337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4337
  · have he : independentCachedBranchMembers4345.filter (independentCachedEdge 2792)=independentCachedBranchMembers4344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4344
def independentCachedBranchMembers4346 : Finset ℕ := ([18,36,40,66,1626,1720,1746,1768,2680,2710,2714,2732,2758,2762,2800,3132,3158,3162,3180,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4346 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4346 5 (fun x => (if x<2758 then (if x<1746 then (if x<66 then (if x<36 then 0 else (if x<40 then 0 else 1)) else (if x<1626 then 1 else (if x<1720 then 0 else 1))) else (if x<2710 then (if x<1768 then 1 else (if x<2680 then 2 else 2)) else (if x<2714 then 3 else (if x<2732 then 0 else 0)))) else (if x<3180 then (if x<3132 then (if x<2762 then 1 else (if x<2800 then 2 else 3)) else (if x<3158 then 1 else (if x<3162 then 1 else 4))) else (if x<3256 then (if x<3214 then 4 else (if x<3252 then 3 else 3)) else (if x<3300 then (if x<3282 then 4 else 0) else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4347 : Finset ℕ := ([18,1720,1746,2710,2714,2800,3132,3158,3162,3214,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4347 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4347 4 (fun x => (if x<3132 then (if x<2710 then (if x<1720 then 0 else (if x<1746 then 1 else 0)) else (if x<2714 then 0 else (if x<2800 then 1 else 1))) else (if x<3214 then (if x<3158 then 2 else (if x<3162 then 0 else 2)) else (if x<3300 then 2 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4348 : Finset ℕ := ([18,36,40,66,1596,1626,1720,1746,1768,2680,2710,2714,2732,2758,2762,2800,3132,3158,3162,3180,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4348 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4348 1596 4
  · have he : independentCachedBranchMembers4348.erase 1596=independentCachedBranchMembers4346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4346
  · have he : independentCachedBranchMembers4348.filter (independentCachedEdge 1596)=independentCachedBranchMembers4347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4347
def independentCachedBranchMembers4349 : Finset ℕ := ([40,66,1626,1768,2680,2710,2762,3132,3158,3214,3256,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4349 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4349 4 (fun x => (if x<2762 then (if x<1768 then (if x<66 then 0 else (if x<1626 then 0 else 1)) else (if x<2680 then 1 else (if x<2710 then 1 else 2))) else (if x<3214 then (if x<3132 then 1 else (if x<3158 then 0 else 0)) else (if x<3282 then (if x<3256 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4350 : Finset ℕ := ([18,36,40,66,1596,1626,1720,1746,1764,1768,2680,2710,2714,2732,2758,2762,2800,3132,3158,3162,3180,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4350 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4350 1764 4
  · have he : independentCachedBranchMembers4350.erase 1764=independentCachedBranchMembers4348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4348
  · have he : independentCachedBranchMembers4350.filter (independentCachedEdge 1764)=independentCachedBranchMembers4349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4349
def independentCachedBranchMembers4351 : Finset ℕ := ([18,36,40,66,3132,3158,3162,3180,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4351 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4351 4 (fun x => (if x<3180 then (if x<66 then (if x<36 then 0 else (if x<40 then 0 else 1)) else (if x<3158 then (if x<3132 then 1 else 1) else (if x<3162 then 1 else 0))) else (if x<3256 then (if x<3214 then 0 else (if x<3252 then 2 else 2)) else (if x<3300 then (if x<3282 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
