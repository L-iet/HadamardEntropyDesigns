/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch176
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8448 : Finset ℕ := ([48,80,132,250,1582,1614,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2732,2738,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8448 2732 4
  · have he : independentCachedBranchMembers8448.erase 2732=independentCachedBranchMembers8446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8446
  · have he : independentCachedBranchMembers8448.filter (independentCachedEdge 2732)=independentCachedBranchMembers8447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8447
def independentCachedBranchMembers8449 : Finset ℕ := ([48,80,132,250,1582,1614,1690,1764,2618,2650,2702,2800,3130,3162,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8449 4 (fun x => (if x<2618 then (if x<1582 then (if x<132 then (if x<80 then 0 else 1) else (if x<250 then 0 else 1)) else (if x<1690 then (if x<1614 then 2 else 3) else (if x<1764 then 2 else 3))) else (if x<3130 then (if x<2702 then (if x<2650 then 0 else 1) else (if x<2800 then 0 else 1)) else (if x<3214 then (if x<3162 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8450 : Finset ℕ := ([48,80,132,250,1582,1614,1644,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2732,2738,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8450 1644 4
  · have he : independentCachedBranchMembers8450.erase 1644=independentCachedBranchMembers8448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8448
  · have he : independentCachedBranchMembers8450.filter (independentCachedEdge 1644)=independentCachedBranchMembers8449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8449
def independentCachedBranchMembers8451 : Finset ℕ := ([48,80,1582,1614,1702,1720,1734,1752,2662,2680,2702,2800,3174,3192,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8451 4 (fun x => (if x<2662 then (if x<1702 then (if x<1582 then (if x<80 then 0 else 1) else (if x<1614 then 1 else 0)) else (if x<1734 then (if x<1720 then 2 else 2) else (if x<1752 then 3 else 3))) else (if x<3174 then (if x<2702 then (if x<2680 then 2 else 2) else (if x<2800 then 0 else 1)) else (if x<3214 then (if x<3192 then 3 else 3) else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8452 : Finset ℕ := ([18,48,80,132,250,1582,1614,1644,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2732,2738,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8452 18 4
  · have he : independentCachedBranchMembers8452.erase 18=independentCachedBranchMembers8450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8450
  · have he : independentCachedBranchMembers8452.filter (independentCachedEdge 18)=independentCachedBranchMembers8451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8451
def independentCachedBranchMembers8453 : Finset ℕ := ([250,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,3130,3162,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8453 4 (fun x => (if x<2618 then (if x<1720 then (if x<1690 then 0 else (if x<1702 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 2) else (if x<1764 then 2 else 3))) else (if x<3130 then (if x<2662 then (if x<2650 then 0 else 3) else (if x<2680 then 1 else 1)) else (if x<3174 then (if x<3162 then 3 else 0) else (if x<3192 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8454 : Finset ℕ := ([250,1690,1720,1752,2662,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8454 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8454 3 (fun x => (if x<1752 then (if x<1690 then 0 else (if x<1720 then 0 else 1)) else (if x<2662 then 2 else (if x<3174 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8455 : Finset ℕ := ([132,250,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,3130,3162,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8455 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8455 132 3
  · have he : independentCachedBranchMembers8455.erase 132=independentCachedBranchMembers8453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8453
  · have he : independentCachedBranchMembers8455.filter (independentCachedEdge 132)=independentCachedBranchMembers8454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8454
def independentCachedBranchMembers8456 : Finset ℕ := ([12,18,48,80,132,250,1582,1614,1644,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2732,2738,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8456 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8456 12 4
  · have he : independentCachedBranchMembers8456.erase 12=independentCachedBranchMembers8452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8452
  · have he : independentCachedBranchMembers8456.filter (independentCachedEdge 12)=independentCachedBranchMembers8455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8455
def independentCachedBranchMembers8457 : Finset ℕ := ([12,18,20,40,48,72,80,130,132,160,190,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2560,2590,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8457 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8457 20 5
  · have he : independentCachedBranchMembers8457.erase 20=independentCachedBranchMembers8431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8431
  · have he : independentCachedBranchMembers8457.filter (independentCachedEdge 20)=independentCachedBranchMembers8456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8456
def independentCachedBranchMembers8458 : Finset ℕ := ([72,252,1590,1622,1644,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8458 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8458 5 (fun x => (if x<2662 then (if x<1702 then (if x<1622 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 2 else (if x<1692 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1734 then 3 else 1)) else (if x<2620 then (if x<1762 then 0 else 3) else (if x<2652 then 1 else 0)))) else (if x<3164 then (if x<2764 then (if x<2680 then 1 else (if x<2710 then 4 else 1)) else (if x<2792 then (if x<2770 then 1 else 4) else (if x<3132 then 0 else 3))) else (if x<3222 then (if x<3174 then 2 else (if x<3192 then 2 else 0)) else (if x<3250 then (if x<3244 then 2 else 2) else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8459 : Finset ℕ := ([252,1590,1622,1692,1720,1752,2662,2764,2792,3174,3244,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8459 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8459 4 (fun x => (if x<2662 then (if x<1692 then (if x<1590 then 0 else (if x<1622 then 1 else 2)) else (if x<1720 then 0 else (if x<1752 then 1 else 2))) else (if x<3174 then (if x<2764 then 1 else (if x<2792 then 0 else 1)) else (if x<3244 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8460 : Finset ℕ := ([72,130,252,1590,1622,1644,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8460 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8460 130 4
  · have he : independentCachedBranchMembers8460.erase 130=independentCachedBranchMembers8458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8458
  · have he : independentCachedBranchMembers8460.filter (independentCachedEdge 130)=independentCachedBranchMembers8459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8459
def independentCachedBranchMembers8461 : Finset ℕ := ([72,1590,1692,1702,1752,1762,2652,2662,2764,3164,3174,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8461 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8461 4 (fun x => (if x<2652 then (if x<1702 then (if x<1590 then 0 else (if x<1692 then 0 else 1)) else (if x<1752 then 1 else (if x<1762 then 2 else 2))) else (if x<3164 then (if x<2662 then 1 else (if x<2764 then 1 else 0)) else (if x<3174 then 2 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8462 : Finset ℕ := ([40,72,130,252,1590,1622,1644,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8462 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8462 40 4
  · have he : independentCachedBranchMembers8462.erase 40=independentCachedBranchMembers8460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8460
  · have he : independentCachedBranchMembers8462.filter (independentCachedEdge 40)=independentCachedBranchMembers8461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8461
def independentCachedBranchMembers8463 : Finset ℕ := ([252,1590,1692,1702,1720,2652,2662,2680,2764,2770,2792,3132,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8463 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8463 4 (fun x => (if x<2680 then (if x<1702 then (if x<1590 then 0 else (if x<1692 then 1 else 0)) else (if x<2652 then (if x<1720 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3132 then (if x<2770 then (if x<2764 then 2 else 3) else (if x<2792 then 3 else 1)) else (if x<3244 then (if x<3222 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8464 : Finset ℕ := ([1692,1720,2662,2770,3132,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8464 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8464 3 (fun x => (if x<2770 then (if x<1720 then 0 else (if x<2662 then 1 else 0)) else (if x<3132 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8465 : Finset ℕ := ([72,252,1590,1692,1702,1720,2652,2662,2680,2764,2770,2792,3132,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8465 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8465 72 3
  · have he : independentCachedBranchMembers8465.erase 72=independentCachedBranchMembers8463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8463
  · have he : independentCachedBranchMembers8465.filter (independentCachedEdge 72)=independentCachedBranchMembers8464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8464
def independentCachedBranchMembers8466 : Finset ℕ := ([40,72,130,252,1590,1622,1644,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8466 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8466 3282 4
  · have he : independentCachedBranchMembers8466.erase 3282=independentCachedBranchMembers8462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8462
  · have he : independentCachedBranchMembers8466.filter (independentCachedEdge 3282)=independentCachedBranchMembers8465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8465
def independentCachedBranchMembers8467 : Finset ℕ := ([130,1622,1702,1720,1762,2620,2662,2680,2710,2764,2770,3164,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8467 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8467 4 (fun x => (if x<2680 then (if x<1720 then (if x<1622 then 0 else (if x<1702 then 1 else 0)) else (if x<2620 then (if x<1762 then 2 else 1) else (if x<2662 then 2 else 1))) else (if x<3164 then (if x<2764 then (if x<2710 then 0 else 3) else (if x<2770 then 3 else 1)) else (if x<3250 then (if x<3244 then 0 else 2) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8468 : Finset ℕ := ([1702,1762,2662,2764,3164,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8468 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8468 3 (fun x => (if x<2764 then (if x<1762 then 0 else (if x<2662 then 1 else 0)) else (if x<3164 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8469 : Finset ℕ := ([40,130,1622,1702,1720,1762,2620,2662,2680,2710,2764,2770,3164,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8469 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8469 40 3
  · have he : independentCachedBranchMembers8469.erase 40=independentCachedBranchMembers8467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8467
  · have he : independentCachedBranchMembers8469.filter (independentCachedEdge 40)=independentCachedBranchMembers8468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8468
def independentCachedBranchMembers8470 : Finset ℕ := ([40,72,130,252,1590,1622,1644,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8470 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8470 3276 4
  · have he : independentCachedBranchMembers8470.erase 3276=independentCachedBranchMembers8466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8466
  · have he : independentCachedBranchMembers8470.filter (independentCachedEdge 3276)=independentCachedBranchMembers8469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8469
def independentCachedBranchMembers8471 : Finset ℕ := ([40,252,1622,1692,1734,1752,2652,2710,2764,2770,3132,3174,3192,3244,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8471 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8471 4 (fun x => (if x<2764 then (if x<1734 then (if x<1622 then (if x<252 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1752 then 2 else 2) else (if x<2710 then 1 else 1))) else (if x<3192 then (if x<3132 then (if x<2770 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8472 : Finset ℕ := ([40,72,130,252,1590,1622,1644,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2738,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8472 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8472 2738 4
  · have he : independentCachedBranchMembers8472.erase 2738=independentCachedBranchMembers8470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8470
  · have he : independentCachedBranchMembers8472.filter (independentCachedEdge 2738)=independentCachedBranchMembers8471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8471
def independentCachedBranchMembers8473 : Finset ℕ := ([72,130,1590,1734,1752,1762,2620,2764,2770,2792,3164,3174,3192,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8473 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8473 4 (fun x => (if x<2770 then (if x<1752 then (if x<1590 then (if x<130 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2620 then (if x<1762 then 2 else 2) else (if x<2764 then 1 else 1))) else (if x<3192 then (if x<3164 then (if x<2792 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3244 then (if x<3222 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8474 : Finset ℕ := ([40,72,130,252,1590,1622,1644,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2732,2738,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8474 2732 4
  · have he : independentCachedBranchMembers8474.erase 2732=independentCachedBranchMembers8472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8472
  · have he : independentCachedBranchMembers8474.filter (independentCachedEdge 2732)=independentCachedBranchMembers8473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8473
def independentCachedBranchMembers8475 : Finset ℕ := ([40,72,130,252,1590,1622,1692,1762,2620,2652,2710,2792,3132,3164,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8475 4 (fun x => (if x<2620 then (if x<1590 then (if x<130 then (if x<72 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1692 then (if x<1622 then 2 else 3) else (if x<1762 then 2 else 3))) else (if x<3132 then (if x<2710 then (if x<2652 then 0 else 1) else (if x<2792 then 0 else 1)) else (if x<3222 then (if x<3164 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8476 : Finset ℕ := ([40,72,130,252,1590,1622,1644,1650,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2710,2732,2738,2764,2770,2792,3132,3164,3174,3192,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8476 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8476 1650 4
  · have he : independentCachedBranchMembers8476.erase 1650=independentCachedBranchMembers8474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8474
  · have he : independentCachedBranchMembers8476.filter (independentCachedEdge 1650)=independentCachedBranchMembers8475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8475
def independentCachedBranchMembers8477 : Finset ℕ := ([252,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,3132,3164,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8477 4 (fun x => (if x<2620 then (if x<1720 then (if x<1692 then 0 else (if x<1702 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 2) else (if x<1762 then 2 else 3))) else (if x<3132 then (if x<2662 then (if x<2652 then 0 else 3) else (if x<2680 then 1 else 1)) else (if x<3174 then (if x<3164 then 3 else 0) else (if x<3192 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8478 : Finset ℕ := ([252,1692,1720,1752,2662,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8478 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8478 3 (fun x => (if x<1752 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2662 then 2 else (if x<3174 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8479 : Finset ℕ := ([130,252,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,3132,3164,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8479 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8479 130 3
  · have he : independentCachedBranchMembers8479.erase 130=independentCachedBranchMembers8477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8477
  · have he : independentCachedBranchMembers8479.filter (independentCachedEdge 130)=independentCachedBranchMembers8478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8478
end EntropyDesigns.QuadraticRefinement
