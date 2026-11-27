/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch48
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4352 : Finset ℕ := ([18,36,40,66,1596,1626,1678,1720,1746,1764,1768,2680,2710,2714,2732,2758,2762,2800,3132,3158,3162,3180,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4352 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4352 1678 4
  · have he : independentCachedBranchMembers4352.erase 1678=independentCachedBranchMembers4350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4350
  · have he : independentCachedBranchMembers4352.filter (independentCachedEdge 1678)=independentCachedBranchMembers4351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4351
def independentCachedBranchMembers4353 : Finset ℕ := ([66,1596,1746,1768,2758,2762,2800,3158,3162,3180,3214,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4353 4 (fun x => (if x<2800 then (if x<1768 then (if x<1596 then 0 else (if x<1746 then 0 else 1)) else (if x<2758 then 1 else (if x<2762 then 0 else 1))) else (if x<3180 then (if x<3158 then 1 else (if x<3162 then 2 else 3)) else (if x<3252 then (if x<3214 then 2 else 2) else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4354 : Finset ℕ := ([66,1768,2762,3158,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4354 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4354 3 (fun x => (if x<3158 then (if x<1768 then 0 else (if x<2762 then 1 else 0)) else (if x<3214 then 1 else (if x<3256 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4355 : Finset ℕ := ([66,1596,1746,1764,1768,2758,2762,2800,3158,3162,3180,3214,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4355 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4355 1764 3
  · have he : independentCachedBranchMembers4355.erase 1764=independentCachedBranchMembers4353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4353
  · have he : independentCachedBranchMembers4355.filter (independentCachedEdge 1764)=independentCachedBranchMembers4354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4354
def independentCachedBranchMembers4356 : Finset ℕ := ([18,36,40,66,1596,1626,1644,1678,1720,1746,1764,1768,2680,2710,2714,2732,2758,2762,2800,3132,3158,3162,3180,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4356 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4356 1644 4
  · have he : independentCachedBranchMembers4356.erase 1644=independentCachedBranchMembers4352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4352
  · have he : independentCachedBranchMembers4356.filter (independentCachedEdge 1644)=independentCachedBranchMembers4355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4355
def independentCachedBranchMembers4357 : Finset ℕ := ([1626,1720,1746,1768,2680,2714,2762,2800,3132,3158,3180,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4357 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4357 4 (fun x => (if x<2800 then (if x<1768 then (if x<1720 then 0 else (if x<1746 then 0 else 1)) else (if x<2714 then (if x<2680 then 1 else 0) else (if x<2762 then 0 else 1))) else (if x<3180 then (if x<3132 then 1 else (if x<3158 then 2 else 2)) else (if x<3252 then (if x<3214 then 3 else 2) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4358 : Finset ℕ := ([1720,1768,2680,2800,3158,3214] : List ℕ).toFinset
theorem independentCachedBranchBound4358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4358 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4358 3 (fun x => (if x<2800 then (if x<1768 then 0 else (if x<2680 then 1 else 0)) else (if x<3158 then 1 else (if x<3214 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4359 : Finset ℕ := ([36,1626,1720,1746,1768,2680,2714,2762,2800,3132,3158,3180,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4359 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4359 36 3
  · have he : independentCachedBranchMembers4359.erase 36=independentCachedBranchMembers4357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4357
  · have he : independentCachedBranchMembers4359.filter (independentCachedEdge 36)=independentCachedBranchMembers4358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4358
def independentCachedBranchMembers4360 : Finset ℕ := ([18,36,40,66,1596,1622,1626,1644,1678,1720,1746,1764,1768,2680,2710,2714,2732,2758,2762,2800,3132,3158,3162,3180,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4360 1622 4
  · have he : independentCachedBranchMembers4360.erase 1622=independentCachedBranchMembers4356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4356
  · have he : independentCachedBranchMembers4360.filter (independentCachedEdge 1622)=independentCachedBranchMembers4359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4359
def independentCachedBranchMembers4361 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,2620,2646,2650,2668,2680,2702,2710,2714,2732,2740,2758,2762,2770,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4361 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4361 2702 5
  · have he : independentCachedBranchMembers4361.erase 2702=independentCachedBranchMembers4345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4345
  · have he : independentCachedBranchMembers4361.filter (independentCachedEdge 2702)=independentCachedBranchMembers4360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4360
def independentCachedBranchMembers4362 : Finset ℕ := ([40,66,130,222,1596,1622,1678,1686,1720,1738,1746,1764,2650,2668,2714,2732,2740,2758,2792,2800,3132,3150,3158,3192,3222,3256,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4362 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4362 5 (fun x => (if x<2714 then (if x<1686 then (if x<222 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1622 then (if x<1596 then 1 else 0) else (if x<1678 then 0 else 1))) else (if x<1746 then (if x<1720 then 2 else (if x<1738 then 2 else 2)) else (if x<2650 then (if x<1764 then 1 else 2) else (if x<2668 then 3 else 3)))) else (if x<3150 then (if x<2758 then (if x<2732 then 1 else (if x<2740 then 0 else 2)) else (if x<2800 then (if x<2792 then 0 else 2) else (if x<3132 then 3 else 4))) else (if x<3256 then (if x<3192 then (if x<3158 then 3 else 4) else (if x<3222 then 3 else 1)) else (if x<3282 then (if x<3274 then 0 else 1) else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4363 : Finset ℕ := ([40,130,1622,1678,1720,1738,2714,2732,2792,3132,3150,3192,3222,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4363 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4363 4 (fun x => (if x<2732 then (if x<1678 then (if x<130 then 0 else (if x<1622 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 2) else (if x<2714 then 2 else 2))) else (if x<3192 then (if x<3132 then (if x<2792 then 1 else 2) else (if x<3150 then 0 else 3)) else (if x<3282 then (if x<3222 then 3 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4364 : Finset ℕ := ([40,66,130,222,1596,1614,1622,1678,1686,1720,1738,1746,1764,2650,2668,2714,2732,2740,2758,2792,2800,3132,3150,3158,3192,3222,3256,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4364 1614 4
  · have he : independentCachedBranchMembers4364.erase 1614=independentCachedBranchMembers4362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4362
  · have he : independentCachedBranchMembers4364.filter (independentCachedEdge 1614)=independentCachedBranchMembers4363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4363
def independentCachedBranchMembers4365 : Finset ℕ := ([40,66,1596,1622,1678,1720,1746,1764,2650,2668,2740,2792,3150,3192,3222,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4365 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4365 4 (fun x => (if x<2650 then (if x<1678 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1746 then (if x<1720 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3150 then (if x<2740 then (if x<2668 then 2 else 2) else (if x<2792 then 3 else 3)) else (if x<3222 then (if x<3192 then 2 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4366 : Finset ℕ := ([40,66,130,222,1596,1614,1622,1678,1686,1720,1738,1746,1764,2650,2668,2714,2732,2740,2758,2792,2800,3132,3150,3158,3192,3214,3222,3256,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4366 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4366 3214 4
  · have he : independentCachedBranchMembers4366.erase 3214=independentCachedBranchMembers4364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4364
  · have he : independentCachedBranchMembers4366.filter (independentCachedEdge 3214)=independentCachedBranchMembers4365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4365
def independentCachedBranchMembers4367 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,2620,2646,2650,2668,2680,2702,2710,2714,2732,2740,2758,2762,2770,2788,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4367 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4367 2788 5
  · have he : independentCachedBranchMembers4367.erase 2788=independentCachedBranchMembers4361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4361
  · have he : independentCachedBranchMembers4367.filter (independentCachedEdge 2788)=independentCachedBranchMembers4366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4366
def independentCachedBranchMembers4368 : Finset ℕ := ([18,36,40,130,1596,1614,1652,1686,1690,1708,1746,1768,2646,2650,2668,2702,2740,2758,2762,2800,3132,3150,3188,3192,3222,3226,3244,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4368 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4368 5 (fun x => (if x<2668 then (if x<1686 then (if x<130 then (if x<36 then 0 else (if x<40 then 0 else 1)) else (if x<1614 then (if x<1596 then 1 else 1) else (if x<1652 then 2 else 2))) else (if x<1746 then (if x<1690 then 1 else (if x<1708 then 0 else 0)) else (if x<2646 then (if x<1768 then 2 else 2) else (if x<2650 then 2 else 0)))) else (if x<3150 then (if x<2758 then (if x<2702 then 0 else (if x<2740 then 3 else 3)) else (if x<2800 then (if x<2762 then 1 else 2) else (if x<3132 then 2 else 4))) else (if x<3226 then (if x<3192 then (if x<3188 then 3 else 3) else (if x<3222 then 1 else 3)) else (if x<3282 then (if x<3244 then 4 else 3) else (if x<3300 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4369 : Finset ℕ := ([40,130,1652,1690,1708,1768,2646,2702,2762,3132,3150,3192,3222,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4369 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4369 4 (fun x => (if x<2702 then (if x<1690 then (if x<130 then 0 else (if x<1652 then 0 else 1)) else (if x<1768 then (if x<1708 then 2 else 1) else (if x<2646 then 2 else 1))) else (if x<3192 then (if x<3132 then (if x<2762 then 1 else 2) else (if x<3150 then 0 else 3)) else (if x<3282 then (if x<3222 then 3 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4370 : Finset ℕ := ([18,36,40,130,1596,1614,1652,1686,1690,1708,1746,1764,1768,2646,2650,2668,2702,2740,2758,2762,2800,3132,3150,3188,3192,3222,3226,3244,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4370 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4370 1764 4
  · have he : independentCachedBranchMembers4370.erase 1764=independentCachedBranchMembers4368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4368
  · have he : independentCachedBranchMembers4370.filter (independentCachedEdge 1764)=independentCachedBranchMembers4369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4369
def independentCachedBranchMembers4371 : Finset ℕ := ([36,130,1596,1614,1652,1690,1746,1768,2650,2702,2740,2758,3192,3222,3244,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4371 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4371 4 (fun x => (if x<2650 then (if x<1652 then (if x<1596 then (if x<130 then 0 else 0) else (if x<1614 then 0 else 1)) else (if x<1746 then (if x<1690 then 1 else 0) else (if x<1768 then 1 else 1))) else (if x<3192 then (if x<2740 then (if x<2702 then 2 else 2) else (if x<2758 then 3 else 3)) else (if x<3244 then (if x<3222 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4372 : Finset ℕ := ([18,36,40,130,1596,1614,1652,1686,1690,1708,1746,1764,1768,2646,2650,2668,2702,2740,2758,2762,2800,3132,3150,3188,3192,3222,3226,3244,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4372 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4372 3304 4
  · have he : independentCachedBranchMembers4372.erase 3304=independentCachedBranchMembers4370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4370
  · have he : independentCachedBranchMembers4372.filter (independentCachedEdge 3304)=independentCachedBranchMembers4371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4371
def independentCachedBranchMembers4373 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,2620,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2758,2762,2770,2788,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4373 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4373 2638 5
  · have he : independentCachedBranchMembers4373.erase 2638=independentCachedBranchMembers4367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4367
  · have he : independentCachedBranchMembers4373.filter (independentCachedEdge 2638)=independentCachedBranchMembers4372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4372
def independentCachedBranchMembers4374 : Finset ℕ := ([40,66,130,222,1614,1652,1678,1720,1746,1768,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3158,3180,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4374 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4374 5 (fun x => (if x<2668 then (if x<1678 then (if x<222 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1614 then 1 else (if x<1652 then 2 else 2))) else (if x<1768 then (if x<1720 then 1 else (if x<1746 then 0 else 0)) else (if x<2646 then (if x<2620 then 2 else 0) else (if x<2650 then 0 else 3)))) else (if x<2800 then (if x<2732 then (if x<2710 then 2 else (if x<2714 then 1 else 4)) else (if x<2758 then 4 else (if x<2762 then 3 else 1))) else (if x<3226 then (if x<3158 then 2 else (if x<3180 then 3 else 4)) else (if x<3270 then (if x<3244 then 1 else 0) else (if x<3274 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4375 : Finset ℕ := ([40,66,130,222,1652,1768,2620,2646,2710,2762,3158,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4375 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4375 4 (fun x => (if x<2620 then (if x<222 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1652 then 1 else (if x<1768 then 2 else 2))) else (if x<2762 then (if x<2646 then 0 else (if x<2710 then 0 else 1)) else (if x<3158 then 1 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4376 : Finset ℕ := ([40,66,130,222,1614,1652,1678,1720,1746,1764,1768,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3158,3180,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4376 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4376 1764 4
  · have he : independentCachedBranchMembers4376.erase 1764=independentCachedBranchMembers4374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4374
  · have he : independentCachedBranchMembers4376.filter (independentCachedEdge 1764)=independentCachedBranchMembers4375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4375
def independentCachedBranchMembers4377 : Finset ℕ := ([40,222,1614,1678,1720,1768,2646,2710,2758,2800,3158,3270] : List ℕ).toFinset
theorem independentCachedBranchBound4377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4377 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4377 4 (fun x => (if x<2646 then (if x<1678 then (if x<222 then 0 else (if x<1614 then 1 else 1)) else (if x<1720 then 2 else (if x<1768 then 0 else 2))) else (if x<2800 then (if x<2710 then 0 else (if x<2758 then 2 else 1)) else (if x<3158 then 2 else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4378 : Finset ℕ := ([36,40,66,130,222,1614,1652,1678,1720,1746,1764,1768,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3158,3180,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4378 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4378 36 4
  · have he : independentCachedBranchMembers4378.erase 36=independentCachedBranchMembers4376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4376
  · have he : independentCachedBranchMembers4378.filter (independentCachedEdge 36)=independentCachedBranchMembers4377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4377
def independentCachedBranchMembers4379 : Finset ℕ := ([66,130,1614,1652,1678,1720,2620,2758,2762,2800,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4379 4 (fun x => (if x<2620 then (if x<1652 then (if x<130 then 0 else (if x<1614 then 1 else 0)) else (if x<1678 then 1 else (if x<1720 then 2 else 2))) else (if x<2800 then (if x<2758 then 1 else (if x<2762 then 0 else 3)) else (if x<3270 then 2 else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4380 : Finset ℕ := ([18,36,40,66,130,222,1614,1652,1678,1720,1746,1764,1768,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3158,3180,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4380 18 4
  · have he : independentCachedBranchMembers4380.erase 18=independentCachedBranchMembers4378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4378
  · have he : independentCachedBranchMembers4380.filter (independentCachedEdge 18)=independentCachedBranchMembers4379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4379
def independentCachedBranchMembers4381 : Finset ℕ := ([66,1614,1652,1720,1764,2620,2650,2710,2732,2762,2800,3158,3180,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound4381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4381 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4381 4 (fun x => (if x<2710 then (if x<1720 then (if x<1614 then 0 else (if x<1652 then 0 else 1)) else (if x<2620 then (if x<1764 then 1 else 2) else (if x<2650 then 1 else 0))) else (if x<3158 then (if x<2762 then (if x<2732 then 3 else 2) else (if x<2800 then 3 else 1)) else (if x<3226 then (if x<3180 then 0 else 2) else (if x<3270 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4382 : Finset ℕ := ([1614,1720,2710,2800,3158,3270] : List ℕ).toFinset
theorem independentCachedBranchBound4382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4382 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4382 3 (fun x => (if x<2800 then (if x<1720 then 0 else (if x<2710 then 1 else 2)) else (if x<3158 then 0 else (if x<3270 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4383 : Finset ℕ := ([36,66,1614,1652,1720,1764,2620,2650,2710,2732,2762,2800,3158,3180,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound4383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4383 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4383 36 3
  · have he : independentCachedBranchMembers4383.erase 36=independentCachedBranchMembers4381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4381
  · have he : independentCachedBranchMembers4383.filter (independentCachedEdge 36)=independentCachedBranchMembers4382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4382
end EntropyDesigns.QuadraticRefinement
