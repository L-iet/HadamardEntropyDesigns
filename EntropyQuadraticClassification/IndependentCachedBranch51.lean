/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch50
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4416 : Finset ℕ := ([1622,1708,2714,2792,3162,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4416 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4416 3 (fun x => (if x<2792 then (if x<1708 then 0 else (if x<2714 then 1 else 2)) else (if x<3162 then 0 else (if x<3282 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4417 : Finset ℕ := ([36,1622,1644,1686,1708,1764,2714,2770,2792,3162,3226,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4417 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4417 3226 3
  · have he : independentCachedBranchMembers4417.erase 3226=independentCachedBranchMembers4415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4415
  · have he : independentCachedBranchMembers4417.filter (independentCachedEdge 3226)=independentCachedBranchMembers4416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4416
def independentCachedBranchMembers4418 : Finset ℕ := ([1644,1686,2714,2770,3162,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4418 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4418 3 (fun x => (if x<2770 then (if x<1686 then 0 else (if x<2714 then 1 else 0)) else (if x<3162 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4419 : Finset ℕ := ([36,1622,1644,1686,1708,1764,2650,2714,2770,2792,3162,3226,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4419 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4419 2650 3
  · have he : independentCachedBranchMembers4419.erase 2650=independentCachedBranchMembers4417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4417
  · have he : independentCachedBranchMembers4419.filter (independentCachedEdge 2650)=independentCachedBranchMembers4418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4418
def independentCachedBranchMembers4420 : Finset ℕ := ([36,1644,1708,1764,2792,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4420 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4420 3 (fun x => (if x<1764 then (if x<1644 then 0 else (if x<1708 then 0 else 1)) else (if x<2792 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4421 : Finset ℕ := ([36,222,1622,1644,1686,1708,1764,2650,2714,2770,2792,3162,3226,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4421 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4421 222 3
  · have he : independentCachedBranchMembers4421.erase 222=independentCachedBranchMembers4419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4419
  · have he : independentCachedBranchMembers4421.filter (independentCachedEdge 222)=independentCachedBranchMembers4420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4420
def independentCachedBranchMembers4422 : Finset ℕ := ([18,36,40,222,1622,1626,1644,1686,1690,1708,1746,1764,1768,2646,2650,2668,2710,2714,2732,2770,2788,2792,3102,3158,3162,3180,3222,3226,3244,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4422 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4422 1768 4
  · have he : independentCachedBranchMembers4422.erase 1768=independentCachedBranchMembers4414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4414
  · have he : independentCachedBranchMembers4422.filter (independentCachedEdge 1768)=independentCachedBranchMembers4421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4421
def independentCachedBranchMembers4423 : Finset ℕ := ([40,222,1622,1686,1746,1764,2646,2710,2770,2788,3102,3162,3180,3226,3244,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4423 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4423 4 (fun x => (if x<2770 then (if x<1746 then (if x<1622 then (if x<222 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1764 then 2 else 2) else (if x<2710 then 1 else 0))) else (if x<3180 then (if x<3102 then (if x<2788 then 3 else 3) else (if x<3162 then 1 else 2)) else (if x<3244 then (if x<3226 then 2 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4424 : Finset ℕ := ([18,36,40,222,1622,1626,1644,1686,1690,1708,1746,1764,1768,2646,2650,2668,2710,2714,2732,2770,2788,2792,3102,3158,3162,3180,3222,3226,3244,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4424 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4424 3300 4
  · have he : independentCachedBranchMembers4424.erase 3300=independentCachedBranchMembers4422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4422
  · have he : independentCachedBranchMembers4424.filter (independentCachedEdge 3300)=independentCachedBranchMembers4423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4423
def independentCachedBranchMembers4425 : Finset ℕ := ([18,36,40,48,66,130,222,252,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,1776,2620,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2758,2762,2770,2788,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4425 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4425 48 5
  · have he : independentCachedBranchMembers4425.erase 48=independentCachedBranchMembers4401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4401
  · have he : independentCachedBranchMembers4425.filter (independentCachedEdge 48)=independentCachedBranchMembers4424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4424
def independentCachedBranchMembers4426 : Finset ℕ := ([66,130,222,1596,1622,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4426 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4426 5 (fun x => (if x<2668 then (if x<1708 then (if x<1596 then (if x<130 then 0 else (if x<222 then 1 else 0)) else (if x<1686 then (if x<1622 then 1 else 0) else (if x<1690 then 1 else 2))) else (if x<1776 then (if x<1734 then 2 else (if x<1738 then 2 else 0)) else (if x<2646 then (if x<2620 then 2 else 3) else (if x<2650 then 3 else 0)))) else (if x<3188 then (if x<2762 then (if x<2710 then 1 else (if x<2758 then 4 else 0)) else (if x<3102 then (if x<2800 then 4 else 3) else (if x<3150 then 3 else 0))) else (if x<3252 then (if x<3192 then 3 else (if x<3214 then 1 else 2)) else (if x<3282 then (if x<3256 then 4 else 2) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4427 : Finset ℕ := ([222,1690,1738,1776,2650,2762,2800,3102,3150,3188,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound4427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4427 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4427 4 (fun x => (if x<2800 then (if x<1776 then (if x<1690 then 0 else (if x<1738 then 0 else 1)) else (if x<2650 then 1 else (if x<2762 then 0 else 2))) else (if x<3188 then (if x<3102 then 2 else (if x<3150 then 0 else 1)) else (if x<3214 then 1 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4428 : Finset ℕ := ([40,66,130,222,1596,1622,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4428 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4428 40 4
  · have he : independentCachedBranchMembers4428.erase 40=independentCachedBranchMembers4426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4426
  · have he : independentCachedBranchMembers4428.filter (independentCachedEdge 40)=independentCachedBranchMembers4427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4427
def independentCachedBranchMembers4429 : Finset ℕ := ([40,66,130,222,1596,1622,1686,1738,2620,2646,2710,2762,3102,3188,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4429 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4429 4 (fun x => (if x<2620 then (if x<1596 then (if x<130 then (if x<66 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1686 then (if x<1622 then 0 else 0) else (if x<1738 then 1 else 1))) else (if x<3102 then (if x<2710 then (if x<2646 then 2 else 2) else (if x<2762 then 3 else 3)) else (if x<3252 then (if x<3188 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4430 : Finset ℕ := ([40,66,130,222,1596,1622,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4430 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4430 3300 4
  · have he : independentCachedBranchMembers4430.erase 3300=independentCachedBranchMembers4428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4428
  · have he : independentCachedBranchMembers4430.filter (independentCachedEdge 3300)=independentCachedBranchMembers4429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4429
def independentCachedBranchMembers4431 : Finset ℕ := ([130,222,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,3102,3150,3188,3192] : List ℕ).toFinset
theorem independentCachedBranchBound4431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4431 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4431 4 (fun x => (if x<2620 then (if x<1708 then (if x<1686 then (if x<222 then 0 else 0) else (if x<1690 then 0 else 1)) else (if x<1738 then (if x<1734 then 1 else 1) else (if x<1776 then 0 else 1))) else (if x<3102 then (if x<2650 then (if x<2646 then 2 else 2) else (if x<2668 then 3 else 3)) else (if x<3188 then (if x<3150 then 2 else 3) else (if x<3192 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4432 : Finset ℕ := ([40,66,130,222,1596,1622,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2732,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4432 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4432 2732 4
  · have he : independentCachedBranchMembers4432.erase 2732=independentCachedBranchMembers4430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4430
  · have he : independentCachedBranchMembers4432.filter (independentCachedEdge 2732)=independentCachedBranchMembers4431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4431
def independentCachedBranchMembers4433 : Finset ℕ := ([40,66,1596,1622,1690,1708,1734,1776,2650,2668,2710,2762,3150,3192,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4433 4 (fun x => (if x<2650 then (if x<1690 then (if x<1596 then (if x<66 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1734 then (if x<1708 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3150 then (if x<2710 then (if x<2668 then 2 else 2) else (if x<2762 then 3 else 3)) else (if x<3252 then (if x<3192 then 2 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4434 : Finset ℕ := ([40,66,130,222,1596,1622,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4434 2714 4
  · have he : independentCachedBranchMembers4434.erase 2714=independentCachedBranchMembers4432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4432
  · have he : independentCachedBranchMembers4434.filter (independentCachedEdge 2714)=independentCachedBranchMembers4433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4433
def independentCachedBranchMembers4435 : Finset ℕ := ([222,1596,1686,1690,1708,2646,2650,2668,2758,2762,2800,3102,3214,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4435 4 (fun x => (if x<2668 then (if x<1690 then (if x<1596 then 0 else (if x<1686 then 1 else 0)) else (if x<2646 then (if x<1708 then 1 else 2) else (if x<2650 then 0 else 2))) else (if x<3102 then (if x<2762 then (if x<2758 then 1 else 3) else (if x<2800 then 1 else 3)) else (if x<3252 then (if x<3214 then 0 else 3) else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4436 : Finset ℕ := ([1686,1690,2668,2800,3102,3214] : List ℕ).toFinset
theorem independentCachedBranchBound4436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4436 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4436 3 (fun x => (if x<2800 then (if x<1690 then 0 else (if x<2668 then 1 else 0)) else (if x<3102 then 2 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4437 : Finset ℕ := ([66,222,1596,1686,1690,1708,2646,2650,2668,2758,2762,2800,3102,3214,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4437 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4437 66 3
  · have he : independentCachedBranchMembers4437.erase 66=independentCachedBranchMembers4435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4435
  · have he : independentCachedBranchMembers4437.filter (independentCachedEdge 66)=independentCachedBranchMembers4436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4436
def independentCachedBranchMembers4438 : Finset ℕ := ([40,66,130,222,1596,1622,1644,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4438 1644 4
  · have he : independentCachedBranchMembers4438.erase 1644=independentCachedBranchMembers4434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4434
  · have he : independentCachedBranchMembers4438.filter (independentCachedEdge 1644)=independentCachedBranchMembers4437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4437
def independentCachedBranchMembers4439 : Finset ℕ := ([130,1622,1690,1708,1738,2620,2650,2668,2710,2758,2800,3188,3214,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4439 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4439 4 (fun x => (if x<2668 then (if x<1708 then (if x<1622 then 0 else (if x<1690 then 1 else 0)) else (if x<2620 then (if x<1738 then 2 else 1) else (if x<2650 then 2 else 1))) else (if x<3188 then (if x<2758 then (if x<2710 then 0 else 3) else (if x<2800 then 1 else 3)) else (if x<3256 then (if x<3214 then 0 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4440 : Finset ℕ := ([1690,1738,2650,2800,3188,3214] : List ℕ).toFinset
theorem independentCachedBranchBound4440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4440 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4440 3 (fun x => (if x<2800 then (if x<1738 then 0 else (if x<2650 then 1 else 0)) else (if x<3188 then 2 else (if x<3214 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4441 : Finset ℕ := ([40,130,1622,1690,1708,1738,2620,2650,2668,2710,2758,2800,3188,3214,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4441 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4441 40 3
  · have he : independentCachedBranchMembers4441.erase 40=independentCachedBranchMembers4439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4439
  · have he : independentCachedBranchMembers4441.filter (independentCachedEdge 40)=independentCachedBranchMembers4440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4440
def independentCachedBranchMembers4442 : Finset ℕ := ([40,66,130,222,1596,1622,1626,1644,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4442 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4442 1626 4
  · have he : independentCachedBranchMembers4442.erase 1626=independentCachedBranchMembers4438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4438
  · have he : independentCachedBranchMembers4442.filter (independentCachedEdge 1626)=independentCachedBranchMembers4441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4441
def independentCachedBranchMembers4443 : Finset ℕ := ([40,222,1622,1686,1734,1776,2646,2710,2758,2800,3102,3150,3192,3214,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4443 4 (fun x => (if x<2758 then (if x<1734 then (if x<1622 then (if x<222 then 0 else 1) else (if x<1686 then 0 else 1)) else (if x<2646 then (if x<1776 then 2 else 2) else (if x<2710 then 1 else 0))) else (if x<3192 then (if x<3102 then (if x<2800 then 3 else 3) else (if x<3150 then 1 else 2)) else (if x<3256 then (if x<3214 then 2 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4444 : Finset ℕ := ([36,40,66,130,222,1596,1622,1626,1644,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4444 36 4
  · have he : independentCachedBranchMembers4444.erase 36=independentCachedBranchMembers4442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4442
  · have he : independentCachedBranchMembers4444.filter (independentCachedEdge 36)=independentCachedBranchMembers4443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4443
def independentCachedBranchMembers4445 : Finset ℕ := ([66,130,1596,1734,1738,1776,2620,2758,2762,2800,3150,3188,3192,3214,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4445 4 (fun x => (if x<2762 then (if x<1738 then (if x<1596 then (if x<130 then 0 else 1) else (if x<1734 then 0 else 1)) else (if x<2620 then (if x<1776 then 2 else 2) else (if x<2758 then 1 else 0))) else (if x<3192 then (if x<3150 then (if x<2800 then 3 else 3) else (if x<3188 then 2 else 2)) else (if x<3252 then (if x<3214 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4446 : Finset ℕ := ([18,36,40,66,130,222,1596,1622,1626,1644,1686,1690,1708,1734,1738,1776,2620,2646,2650,2668,2710,2714,2732,2758,2762,2800,3102,3150,3188,3192,3214,3252,3256,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4446 18 4
  · have he : independentCachedBranchMembers4446.erase 18=independentCachedBranchMembers4444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4444
  · have he : independentCachedBranchMembers4446.filter (independentCachedEdge 18)=independentCachedBranchMembers4445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4445
def independentCachedBranchMembers4447 : Finset ℕ := ([18,36,40,48,66,130,222,252,1596,1614,1622,1626,1644,1652,1678,1686,1690,1708,1720,1734,1738,1746,1764,1768,1776,2620,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2758,2762,2770,2788,2792,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4447 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4447 3312 5
  · have he : independentCachedBranchMembers4447.erase 3312=independentCachedBranchMembers4425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4425
  · have he : independentCachedBranchMembers4447.filter (independentCachedEdge 3312)=independentCachedBranchMembers4446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4446
end EntropyDesigns.QuadraticRefinement
