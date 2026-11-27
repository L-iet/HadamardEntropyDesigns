/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch114
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6464 : Finset ℕ := ([48,66,144,252,1582,1628,1642,1652,1678,1720,1738,1748,1762,2620,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6464 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6464 3288 4
  · have he : independentCachedBranchMembers6464.erase 3288=independentCachedBranchMembers6460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6460
  · have he : independentCachedBranchMembers6464.filter (independentCachedEdge 3288)=independentCachedBranchMembers6463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6463
def independentCachedBranchMembers6465 : Finset ℕ := ([252,1582,1628,1642,1652,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6465 4 (fun x => (if x<2740 then (if x<1642 then (if x<1582 then 0 else (if x<1628 then 1 else 0)) else (if x<2716 then (if x<1652 then 2 else 1) else (if x<2730 then 0 else 1))) else (if x<3132 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 3 else 1)) else (if x<3174 then (if x<3150 then 0 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6466 : Finset ℕ := ([1628,1652,2730,2758,3132,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6466 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6466 3 (fun x => (if x<2758 then (if x<1652 then 0 else (if x<2730 then 1 else 0)) else (if x<3132 then 2 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6467 : Finset ℕ := ([144,252,1582,1628,1642,1652,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6467 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6467 144 3
  · have he : independentCachedBranchMembers6467.erase 144=independentCachedBranchMembers6465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6465
  · have he : independentCachedBranchMembers6467.filter (independentCachedEdge 144)=independentCachedBranchMembers6466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6466
def independentCachedBranchMembers6468 : Finset ℕ := ([48,66,144,252,1582,1628,1642,1652,1678,1720,1738,1748,1762,2620,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3270,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6468 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6468 3270 4
  · have he : independentCachedBranchMembers6468.erase 3270=independentCachedBranchMembers6464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6464
  · have he : independentCachedBranchMembers6468.filter (independentCachedEdge 3270)=independentCachedBranchMembers6467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6467
def independentCachedBranchMembers6469 : Finset ℕ := ([48,66,144,252,1582,1628,1678,1762,2620,2638,2716,2800,3132,3150,3228,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6469 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6469 4 (fun x => (if x<2620 then (if x<1582 then (if x<144 then (if x<66 then 0 else 0) else (if x<252 then 1 else 1)) else (if x<1678 then (if x<1628 then 2 else 2) else (if x<1762 then 3 else 3))) else (if x<3132 then (if x<2716 then (if x<2638 then 0 else 0) else (if x<2800 then 1 else 1)) else (if x<3228 then (if x<3150 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6470 : Finset ℕ := ([48,66,144,252,1582,1628,1642,1652,1678,1702,1720,1738,1748,1762,2620,2638,2716,2730,2740,2758,2776,2800,3132,3150,3174,3192,3228,3242,3252,3270,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6470 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6470 1702 4
  · have he : independentCachedBranchMembers6470.erase 1702=independentCachedBranchMembers6468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6468
  · have he : independentCachedBranchMembers6470.filter (independentCachedEdge 1702)=independentCachedBranchMembers6469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6469
def independentCachedBranchMembers6471 : Finset ℕ := ([18,36,48,66,72,132,144,192,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6471 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6471 18 5
  · have he : independentCachedBranchMembers6471.erase 18=independentCachedBranchMembers6445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6445
  · have he : independentCachedBranchMembers6471.filter (independentCachedEdge 18)=independentCachedBranchMembers6470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6470
def independentCachedBranchMembers6472 : Finset ℕ := ([246,1594,1622,1642,1652,1690,1702,1748,1768,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6472 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6472 5 (fun x => (if x<2740 then (if x<1690 then (if x<1622 then (if x<1594 then 0 else 1) else (if x<1642 then 0 else (if x<1652 then 2 else 1))) else (if x<1768 then (if x<1702 then 2 else (if x<1748 then 0 else 3)) else (if x<2710 then 1 else (if x<2730 then 0 else 1)))) else (if x<3162 then (if x<2776 then (if x<2758 then 3 else 3) else (if x<2788 then 3 else (if x<3126 then 1 else 0))) else (if x<3222 then (if x<3174 then 2 else (if x<3192 then 2 else 4)) else (if x<3242 then 2 else (if x<3300 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6473 : Finset ℕ := ([1622,1652,1690,1768,2730,2776,3126,3174,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6473 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6473 4 (fun x => (if x<2730 then (if x<1690 then (if x<1652 then 0 else 1) else (if x<1768 then 0 else 1)) else (if x<3126 then (if x<2776 then 0 else 2) else (if x<3174 then 1 else (if x<3242 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6474 : Finset ℕ := ([132,246,1594,1622,1642,1652,1690,1702,1748,1768,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6474 132 4
  · have he : independentCachedBranchMembers6474.erase 132=independentCachedBranchMembers6472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6472
  · have he : independentCachedBranchMembers6474.filter (independentCachedEdge 132)=independentCachedBranchMembers6473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6473
def independentCachedBranchMembers6475 : Finset ℕ := ([1594,1622,1690,1768,2730,2740,2758,2776,3126,3162,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6475 4 (fun x => (if x<2758 then (if x<1768 then (if x<1622 then 0 else (if x<1690 then 0 else 1)) else (if x<2730 then 1 else (if x<2740 then 0 else 2))) else (if x<3162 then (if x<2776 then 0 else (if x<3126 then 1 else 2)) else (if x<3222 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6476 : Finset ℕ := ([132,246,1594,1622,1642,1652,1690,1702,1748,1768,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6476 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6476 3252 4
  · have he : independentCachedBranchMembers6476.erase 3252=independentCachedBranchMembers6474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6474
  · have he : independentCachedBranchMembers6476.filter (independentCachedEdge 3252)=independentCachedBranchMembers6475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6475
def independentCachedBranchMembers6477 : Finset ℕ := ([246,1652,1748,1768,2740,2776,2788,3126,3162,3174,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6477 4 (fun x => (if x<2788 then (if x<1768 then (if x<1652 then 0 else (if x<1748 then 0 else 1)) else (if x<2740 then 1 else (if x<2776 then 0 else 1))) else (if x<3174 then (if x<3126 then 1 else (if x<3162 then 0 else 2)) else (if x<3222 then 2 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6478 : Finset ℕ := ([132,246,1594,1622,1642,1652,1690,1702,1748,1768,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6478 2650 4
  · have he : independentCachedBranchMembers6478.erase 2650=independentCachedBranchMembers6476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6476
  · have he : independentCachedBranchMembers6478.filter (independentCachedEdge 2650)=independentCachedBranchMembers6477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6477
def independentCachedBranchMembers6479 : Finset ℕ := ([132,1642,1690,1748,2710,2740,2776,3126,3162,3192,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6479 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6479 4 (fun x => (if x<2776 then (if x<1748 then (if x<1642 then 0 else (if x<1690 then 0 else 1)) else (if x<2710 then 1 else (if x<2740 then 0 else 2))) else (if x<3192 then (if x<3126 then 1 else (if x<3162 then 2 else 2)) else (if x<3242 then 0 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6480 : Finset ℕ := ([132,246,1594,1622,1642,1652,1690,1702,1748,1768,2614,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6480 2614 4
  · have he : independentCachedBranchMembers6480.erase 2614=independentCachedBranchMembers6478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6478
  · have he : independentCachedBranchMembers6480.filter (independentCachedEdge 2614)=independentCachedBranchMembers6479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6479
def independentCachedBranchMembers6481 : Finset ℕ := ([132,246,1642,1652,1690,1768,2710,2788,3174,3192,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6481 4 (fun x => (if x<2710 then (if x<1652 then (if x<246 then 0 else (if x<1642 then 0 else 1)) else (if x<1690 then 1 else (if x<1768 then 2 else 2))) else (if x<3192 then (if x<2788 then 0 else (if x<3174 then 0 else 1)) else (if x<3222 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6482 : Finset ℕ := ([132,246,1594,1622,1642,1652,1690,1702,1738,1748,1768,2614,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6482 1738 4
  · have he : independentCachedBranchMembers6482.erase 1738=independentCachedBranchMembers6480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6480
  · have he : independentCachedBranchMembers6482.filter (independentCachedEdge 1738)=independentCachedBranchMembers6481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6481
def independentCachedBranchMembers6483 : Finset ℕ := ([246,1594,1622,1652,1690,1748,2730,2758,2788,3174,3242,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6483 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6483 4 (fun x => (if x<2730 then (if x<1652 then (if x<1594 then 0 else (if x<1622 then 1 else 0)) else (if x<1690 then 1 else (if x<1748 then 2 else 2))) else (if x<3174 then (if x<2758 then 1 else (if x<2788 then 0 else 1)) else (if x<3242 then 0 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6484 : Finset ℕ := ([72,132,246,1594,1622,1642,1652,1690,1702,1738,1748,1768,2614,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6484 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6484 72 4
  · have he : independentCachedBranchMembers6484.erase 72=independentCachedBranchMembers6482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6482
  · have he : independentCachedBranchMembers6484.filter (independentCachedEdge 72)=independentCachedBranchMembers6483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6483
def independentCachedBranchMembers6485 : Finset ℕ := ([132,1594,1622,1642,1748,1768,2710,2730,2758,3192,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6485 4 (fun x => (if x<2710 then (if x<1642 then (if x<1594 then 0 else (if x<1622 then 0 else 1)) else (if x<1748 then 1 else (if x<1768 then 2 else 2))) else (if x<3192 then (if x<2730 then 1 else (if x<2758 then 1 else 0)) else (if x<3222 then 0 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6486 : Finset ℕ := ([36,72,132,246,1594,1622,1642,1652,1690,1702,1738,1748,1768,2614,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6486 36 4
  · have he : independentCachedBranchMembers6486.erase 36=independentCachedBranchMembers6484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6484
  · have he : independentCachedBranchMembers6486.filter (independentCachedEdge 36)=independentCachedBranchMembers6485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6485
def independentCachedBranchMembers6487 : Finset ℕ := ([246,1594,1622,1642,1652,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6487 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6487 4 (fun x => (if x<2740 then (if x<1642 then (if x<1594 then 0 else (if x<1622 then 1 else 0)) else (if x<2710 then (if x<1652 then 2 else 1) else (if x<2730 then 0 else 1))) else (if x<3126 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2788 then 3 else 1)) else (if x<3174 then (if x<3162 then 0 else 2) else (if x<3192 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6488 : Finset ℕ := ([1622,1652,2730,2776,3126,3174] : List ℕ).toFinset
theorem independentCachedBranchBound6488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6488 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6488 3 (fun x => (if x<2776 then (if x<1652 then 0 else (if x<2730 then 1 else 0)) else (if x<3126 then 2 else (if x<3174 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6489 : Finset ℕ := ([132,246,1594,1622,1642,1652,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound6489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6489 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6489 132 3
  · have he : independentCachedBranchMembers6489.erase 132=independentCachedBranchMembers6487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6487
  · have he : independentCachedBranchMembers6489.filter (independentCachedEdge 132)=independentCachedBranchMembers6488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6488
def independentCachedBranchMembers6490 : Finset ℕ := ([36,72,132,246,1594,1622,1642,1652,1690,1702,1738,1748,1768,2614,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6490 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6490 3288 4
  · have he : independentCachedBranchMembers6490.erase 3288=independentCachedBranchMembers6486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6486
  · have he : independentCachedBranchMembers6490.filter (independentCachedEdge 3288)=independentCachedBranchMembers6489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6489
def independentCachedBranchMembers6491 : Finset ℕ := ([72,1642,1652,1690,1768,2614,2650,2730,2740,2758,2776,3174,3192,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6491 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6491 4 (fun x => (if x<2730 then (if x<1690 then (if x<1642 then 0 else (if x<1652 then 0 else 1)) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2650 then 1 else 0))) else (if x<3174 then (if x<2758 then (if x<2740 then 1 else 3) else (if x<2776 then 3 else 2)) else (if x<3222 then (if x<3192 then 2 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6492 : Finset ℕ := ([1642,1768,2730,2758,3192,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6492 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6492 3 (fun x => (if x<2758 then (if x<1768 then 0 else (if x<2730 then 1 else 0)) else (if x<3192 then 2 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6493 : Finset ℕ := ([36,72,1642,1652,1690,1768,2614,2650,2730,2740,2758,2776,3174,3192,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6493 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6493 36 3
  · have he : independentCachedBranchMembers6493.erase 36=independentCachedBranchMembers6491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6491
  · have he : independentCachedBranchMembers6493.filter (independentCachedEdge 36)=independentCachedBranchMembers6492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6492
def independentCachedBranchMembers6494 : Finset ℕ := ([36,72,132,246,1594,1622,1642,1652,1690,1702,1738,1748,1768,2614,2650,2710,2730,2740,2758,2776,2788,3126,3162,3174,3192,3222,3242,3252,3270,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6494 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6494 3270 4
  · have he : independentCachedBranchMembers6494.erase 3270=independentCachedBranchMembers6490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6490
  · have he : independentCachedBranchMembers6494.filter (independentCachedEdge 3270)=independentCachedBranchMembers6493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6493
def independentCachedBranchMembers6495 : Finset ℕ := ([36,72,132,246,1594,1622,1690,1768,2614,2650,2710,2788,3126,3162,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6495 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6495 4 (fun x => (if x<2614 then (if x<1594 then (if x<132 then (if x<72 then 0 else 0) else (if x<246 then 1 else 1)) else (if x<1690 then (if x<1622 then 2 else 2) else (if x<1768 then 3 else 3))) else (if x<3126 then (if x<2710 then (if x<2650 then 0 else 0) else (if x<2788 then 1 else 1)) else (if x<3222 then (if x<3162 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
