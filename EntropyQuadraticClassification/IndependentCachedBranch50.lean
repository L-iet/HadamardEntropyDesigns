/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch49
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4384 : Finset ℕ := ([18,36,40,66,130,222,1614,1652,1678,1720,1746,1764,1768,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3158,3180,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4384 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4384 3222 4
  · have he : independentCachedBranchMembers4384.erase 3222=independentCachedBranchMembers4380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4380
  · have he : independentCachedBranchMembers4384.filter (independentCachedEdge 3222)=independentCachedBranchMembers4383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4383
def independentCachedBranchMembers4385 : Finset ℕ := ([130,1652,1678,1720,1768,2620,2650,2668,2710,2758,2800,3158,3226,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4385 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4385 4 (fun x => (if x<2668 then (if x<1720 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<2620 then (if x<1768 then 1 else 2) else (if x<2650 then 0 else 3))) else (if x<3158 then (if x<2758 then (if x<2710 then 2 else 3) else (if x<2800 then 1 else 1)) else (if x<3244 then (if x<3226 then 3 else 3) else (if x<3274 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4386 : Finset ℕ := ([1652,1678,2650,2800,3226,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4386 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4386 3 (fun x => (if x<2800 then (if x<1678 then 0 else (if x<2650 then 1 else 2)) else (if x<3226 then 0 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4387 : Finset ℕ := ([40,130,1652,1678,1720,1768,2620,2650,2668,2710,2758,2800,3158,3226,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4387 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4387 40 3
  · have he : independentCachedBranchMembers4387.erase 40=independentCachedBranchMembers4385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4385
  · have he : independentCachedBranchMembers4387.filter (independentCachedEdge 40)=independentCachedBranchMembers4386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4386
def independentCachedBranchMembers4388 : Finset ℕ := ([18,36,40,66,130,222,1614,1652,1678,1720,1746,1764,1768,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3158,3162,3180,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4388 3162 4
  · have he : independentCachedBranchMembers4388.erase 3162=independentCachedBranchMembers4384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4384
  · have he : independentCachedBranchMembers4388.filter (independentCachedEdge 3162)=independentCachedBranchMembers4387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4387
def independentCachedBranchMembers4389 : Finset ℕ := ([222,1614,1678,1764,1768,2620,2646,2650,2710,2714,2800,3180,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4389 4 (fun x => (if x<2650 then (if x<1764 then (if x<1614 then 0 else (if x<1678 then 0 else 1)) else (if x<2620 then (if x<1768 then 1 else 2) else (if x<2646 then 3 else 0))) else (if x<3180 then (if x<2714 then (if x<2710 then 3 else 2) else (if x<2800 then 1 else 1)) else (if x<3270 then (if x<3244 then 2 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4390 : Finset ℕ := ([1614,1678,2620,2800,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4390 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4390 3 (fun x => (if x<2800 then (if x<1678 then 0 else (if x<2620 then 1 else 2)) else (if x<3270 then 0 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4391 : Finset ℕ := ([18,222,1614,1678,1764,1768,2620,2646,2650,2710,2714,2800,3180,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4391 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4391 18 3
  · have he : independentCachedBranchMembers4391.erase 18=independentCachedBranchMembers4389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4389
  · have he : independentCachedBranchMembers4391.filter (independentCachedEdge 18)=independentCachedBranchMembers4390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4390
def independentCachedBranchMembers4392 : Finset ℕ := ([18,36,40,66,130,222,1614,1652,1678,1720,1746,1764,1768,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3132,3158,3162,3180,3222,3226,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4392 3132 4
  · have he : independentCachedBranchMembers4392.erase 3132=independentCachedBranchMembers4388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4388
  · have he : independentCachedBranchMembers4392.filter (independentCachedEdge 3132)=independentCachedBranchMembers4391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4391
def independentCachedBranchMembers4393 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,1776,2620,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2758,2762,2770,2788,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4393 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4393 1776 5
  · have he : independentCachedBranchMembers4393.erase 1776=independentCachedBranchMembers4373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4373
  · have he : independentCachedBranchMembers4393.filter (independentCachedEdge 1776)=independentCachedBranchMembers4392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4392
def independentCachedBranchMembers4394 : Finset ℕ := ([18,66,130,222,1614,1622,1626,1686,1690,1734,1738,1746,2638,2646,2650,2702,2710,2714,2758,2762,2770,3102,3158,3162,3214,3226,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4394 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4394 5 (fun x => (if x<2650 then (if x<1686 then (if x<222 then (if x<66 then 0 else (if x<130 then 1 else 2)) else (if x<1622 then (if x<1614 then 0 else 1) else (if x<1626 then 0 else 3))) else (if x<1738 then (if x<1690 then 2 else (if x<1734 then 0 else 3)) else (if x<2638 then (if x<1746 then 2 else 1) else (if x<2646 then 3 else 1)))) else (if x<3102 then (if x<2714 then (if x<2702 then 0 else (if x<2710 then 2 else 0)) else (if x<2762 then (if x<2758 then 4 else 4) else (if x<2770 then 1 else 2))) else (if x<3226 then (if x<3162 then (if x<3158 then 0 else 3) else (if x<3214 then 1 else 4)) else (if x<3274 then (if x<3270 then 2 else 1) else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4395 : Finset ℕ := ([66,1614,1626,1686,1738,2638,2650,2710,2762,3102,3158,3214,3226,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4395 4 (fun x => (if x<2710 then (if x<1686 then (if x<1614 then 0 else (if x<1626 then 0 else 1)) else (if x<2638 then (if x<1738 then 1 else 2) else (if x<2650 then 2 else 0))) else (if x<3214 then (if x<3102 then (if x<2762 then 3 else 3) else (if x<3158 then 1 else 0)) else (if x<3270 then (if x<3226 then 2 else 3) else (if x<3282 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4396 : Finset ℕ := ([18,66,130,222,1614,1622,1626,1686,1690,1734,1738,1746,2638,2646,2650,2702,2710,2714,2758,2762,2770,3102,3158,3162,3214,3222,3226,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4396 3222 4
  · have he : independentCachedBranchMembers4396.erase 3222=independentCachedBranchMembers4394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4394
  · have he : independentCachedBranchMembers4396.filter (independentCachedEdge 3222)=independentCachedBranchMembers4395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4395
def independentCachedBranchMembers4397 : Finset ℕ := ([18,66,1614,1686,1690,1734,1738,2646,2650,2702,2770,3158,3162,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4397 4 (fun x => (if x<2646 then (if x<1686 then (if x<66 then 0 else (if x<1614 then 1 else 1)) else (if x<1734 then (if x<1690 then 0 else 2) else (if x<1738 then 2 else 3))) else (if x<3158 then (if x<2702 then (if x<2650 then 0 else 1) else (if x<2770 then 2 else 2)) else (if x<3214 then (if x<3162 then 1 else 3) else (if x<3282 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4398 : Finset ℕ := ([18,66,130,222,1614,1622,1626,1678,1686,1690,1734,1738,1746,2638,2646,2650,2702,2710,2714,2758,2762,2770,3102,3158,3162,3214,3222,3226,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4398 1678 4
  · have he : independentCachedBranchMembers4398.erase 1678=independentCachedBranchMembers4396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4396
  · have he : independentCachedBranchMembers4398.filter (independentCachedEdge 1678)=independentCachedBranchMembers4397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4397
def independentCachedBranchMembers4399 : Finset ℕ := ([18,130,1614,1686,1690,1746,2638,2710,2714,2770,3102,3158,3162,3214,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound4399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4399 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4399 4 (fun x => (if x<2714 then (if x<1690 then (if x<1614 then (if x<130 then 0 else 1) else (if x<1686 then 2 else 0)) else (if x<2638 then (if x<1746 then 1 else 2) else (if x<2710 then 3 else 1))) else (if x<3162 then (if x<3102 then (if x<2770 then 0 else 3) else (if x<3158 then 0 else 2)) else (if x<3270 then (if x<3214 then 3 else 1) else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4400 : Finset ℕ := ([18,66,130,222,1614,1622,1626,1678,1686,1690,1734,1738,1746,2638,2646,2650,2702,2710,2714,2758,2762,2770,3102,3150,3158,3162,3214,3222,3226,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4400 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4400 3150 4
  · have he : independentCachedBranchMembers4400.erase 3150=independentCachedBranchMembers4398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4398
  · have he : independentCachedBranchMembers4400.filter (independentCachedEdge 3150)=independentCachedBranchMembers4399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4399
def independentCachedBranchMembers4401 : Finset ℕ := ([18,36,40,66,130,222,252,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,1776,2620,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2758,2762,2770,2788,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4401 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4401 252 5
  · have he : independentCachedBranchMembers4401.erase 252=independentCachedBranchMembers4393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4393
  · have he : independentCachedBranchMembers4401.filter (independentCachedEdge 252)=independentCachedBranchMembers4400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4400
def independentCachedBranchMembers4402 : Finset ℕ := ([18,36,40,222,1622,1686,1690,1708,1746,1764,2646,2650,2668,2714,2770,2788,2792,3102,3162,3180,3222,3226,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4402 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4402 5 (fun x => (if x<2668 then (if x<1690 then (if x<222 then (if x<36 then 0 else (if x<40 then 0 else 1)) else (if x<1622 then 2 else (if x<1686 then 1 else 2))) else (if x<1764 then (if x<1708 then 0 else (if x<1746 then 0 else 3)) else (if x<2646 then 3 else (if x<2650 then 2 else 0)))) else (if x<3162 then (if x<2788 then (if x<2714 then 0 else (if x<2770 then 2 else 1)) else (if x<2792 then 4 else (if x<3102 then 1 else 2))) else (if x<3226 then (if x<3180 then 3 else (if x<3222 then 3 else 1)) else (if x<3282 then (if x<3244 then 4 else 1) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4403 : Finset ℕ := ([36,1686,1708,1764,2646,2668,2714,2770,2792,3162,3222,3244] : List ℕ).toFinset
theorem independentCachedBranchBound4403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4403 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4403 4 (fun x => (if x<2714 then (if x<1764 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<2646 then 1 else (if x<2668 then 2 else 0))) else (if x<3162 then (if x<2770 then 1 else (if x<2792 then 3 else 1)) else (if x<3222 then 2 else (if x<3244 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4404 : Finset ℕ := ([18,36,40,222,1622,1686,1690,1708,1746,1764,2646,2650,2668,2710,2714,2770,2788,2792,3102,3162,3180,3222,3226,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4404 2710 4
  · have he : independentCachedBranchMembers4404.erase 2710=independentCachedBranchMembers4402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4402
  · have he : independentCachedBranchMembers4404.filter (independentCachedEdge 2710)=independentCachedBranchMembers4403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4403
def independentCachedBranchMembers4405 : Finset ℕ := ([222,1686,1690,1708,1746,1764,2646,2650,2668,3102,3162,3180] : List ℕ).toFinset
theorem independentCachedBranchBound4405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4405 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4405 4 (fun x => (if x<2646 then (if x<1708 then (if x<1686 then 0 else (if x<1690 then 0 else 1)) else (if x<1746 then 1 else (if x<1764 then 2 else 2))) else (if x<3102 then (if x<2650 then 0 else (if x<2668 then 1 else 1)) else (if x<3162 then 0 else (if x<3180 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4406 : Finset ℕ := ([18,36,40,222,1622,1644,1686,1690,1708,1746,1764,2646,2650,2668,2710,2714,2770,2788,2792,3102,3162,3180,3222,3226,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4406 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4406 1644 4
  · have he : independentCachedBranchMembers4406.erase 1644=independentCachedBranchMembers4404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4404
  · have he : independentCachedBranchMembers4406.filter (independentCachedEdge 1644)=independentCachedBranchMembers4405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4405
def independentCachedBranchMembers4407 : Finset ℕ := ([222,1686,1690,1708,2646,2650,2668,2770,2788,2792,3102,3222,3226,3244] : List ℕ).toFinset
theorem independentCachedBranchBound4407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4407 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4407 4 (fun x => (if x<2770 then (if x<1708 then (if x<1686 then 0 else (if x<1690 then 0 else 1)) else (if x<2650 then (if x<2646 then 1 else 0) else (if x<2668 then 1 else 1))) else (if x<3102 then (if x<2788 then 2 else (if x<2792 then 2 else 3)) else (if x<3226 then (if x<3222 then 0 else 3) else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4408 : Finset ℕ := ([18,36,40,222,1622,1644,1686,1690,1708,1746,1764,2646,2650,2668,2710,2714,2732,2770,2788,2792,3102,3162,3180,3222,3226,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4408 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4408 2732 4
  · have he : independentCachedBranchMembers4408.erase 2732=independentCachedBranchMembers4406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4406
  · have he : independentCachedBranchMembers4408.filter (independentCachedEdge 2732)=independentCachedBranchMembers4407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4407
def independentCachedBranchMembers4409 : Finset ℕ := ([40,1622,1690,1708,1746,1764,2650,2668,2710,2792,3162,3180,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4409 4 (fun x => (if x<2668 then (if x<1708 then (if x<1622 then 0 else (if x<1690 then 0 else 1)) else (if x<1764 then (if x<1746 then 1 else 2) else (if x<2650 then 2 else 1))) else (if x<3162 then (if x<2710 then 1 else (if x<2792 then 0 else 3)) else (if x<3222 then (if x<3180 then 2 else 2) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4410 : Finset ℕ := ([18,36,40,222,1622,1626,1644,1686,1690,1708,1746,1764,2646,2650,2668,2710,2714,2732,2770,2788,2792,3102,3162,3180,3222,3226,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4410 1626 4
  · have he : independentCachedBranchMembers4410.erase 1626=independentCachedBranchMembers4408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4408
  · have he : independentCachedBranchMembers4410.filter (independentCachedEdge 1626)=independentCachedBranchMembers4409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4409
def independentCachedBranchMembers4411 : Finset ℕ := ([36,1622,1690,1764,2646,2668,2714,2788,3102,3162,3222,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4411 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4411 4 (fun x => (if x<2788 then (if x<1764 then (if x<1622 then 0 else (if x<1690 then 1 else 0)) else (if x<2668 then (if x<2646 then 1 else 2) else (if x<2714 then 0 else 2))) else (if x<3222 then (if x<3102 then 3 else (if x<3162 then 1 else 2)) else (if x<3282 then (if x<3244 then 2 else 1) else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4412 : Finset ℕ := ([1690,1764,2646,2668,3102,3162] : List ℕ).toFinset
theorem independentCachedBranchBound4412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4412 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4412 3 (fun x => (if x<2668 then (if x<1764 then 0 else (if x<2646 then 1 else 2)) else (if x<3102 then 0 else (if x<3162 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4413 : Finset ℕ := ([36,1622,1644,1690,1764,2646,2668,2714,2788,3102,3162,3222,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4413 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4413 1644 3
  · have he : independentCachedBranchMembers4413.erase 1644=independentCachedBranchMembers4411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4411
  · have he : independentCachedBranchMembers4413.filter (independentCachedEdge 1644)=independentCachedBranchMembers4412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4412
def independentCachedBranchMembers4414 : Finset ℕ := ([18,36,40,222,1622,1626,1644,1686,1690,1708,1746,1764,2646,2650,2668,2710,2714,2732,2770,2788,2792,3102,3158,3162,3180,3222,3226,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4414 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4414 3158 4
  · have he : independentCachedBranchMembers4414.erase 3158=independentCachedBranchMembers4410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4410
  · have he : independentCachedBranchMembers4414.filter (independentCachedEdge 3158)=independentCachedBranchMembers4413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4413
def independentCachedBranchMembers4415 : Finset ℕ := ([36,1622,1644,1686,1708,1764,2714,2770,2792,3162,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4415 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4415 4 (fun x => (if x<2714 then (if x<1686 then (if x<1622 then 0 else (if x<1644 then 1 else 0)) else (if x<1708 then 2 else (if x<1764 then 2 else 1))) else (if x<3162 then (if x<2770 then 0 else (if x<2792 then 2 else 1)) else (if x<3282 then 3 else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
