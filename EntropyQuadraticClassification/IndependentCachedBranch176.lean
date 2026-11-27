/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch175
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8416 : Finset ℕ := ([48,132,192,222,1582,1590,1642,1650,1652,1690,1692,1734,1752,2618,2662,2680,2702,2762,2764,2770,2772,3130,3132,3174,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8416 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8416 3282 4
  · have he : independentCachedBranchMembers8416.erase 3282=independentCachedBranchMembers8412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8412
  · have he : independentCachedBranchMembers8416.filter (independentCachedEdge 3282)=independentCachedBranchMembers8415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8415
def independentCachedBranchMembers8417 : Finset ℕ := ([222,1582,1590,1690,1692,2662,2680,2762,2764,2770,2772,3130,3132,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8417 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8417 4 (fun x => (if x<2762 then (if x<1690 then (if x<1582 then 0 else (if x<1590 then 1 else 2)) else (if x<2662 then (if x<1692 then 0 else 1) else (if x<2680 then 1 else 3))) else (if x<3130 then (if x<2770 then (if x<2764 then 0 else 2) else (if x<2772 then 3 else 1)) else (if x<3214 then (if x<3132 then 2 else 3) else (if x<3222 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8418 : Finset ℕ := ([1690,1692,2662,2680,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8418 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8418 3 (fun x => (if x<2680 then (if x<1692 then 0 else (if x<2662 then 1 else 0)) else (if x<3214 then 2 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8419 : Finset ℕ := ([192,222,1582,1590,1690,1692,2662,2680,2762,2764,2770,2772,3130,3132,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8419 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8419 192 3
  · have he : independentCachedBranchMembers8419.erase 192=independentCachedBranchMembers8417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8417
  · have he : independentCachedBranchMembers8419.filter (independentCachedEdge 192)=independentCachedBranchMembers8418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8418
def independentCachedBranchMembers8420 : Finset ℕ := ([48,132,192,222,1582,1590,1642,1650,1652,1690,1692,1734,1752,2618,2662,2680,2702,2762,2764,2770,2772,3130,3132,3174,3192,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8420 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8420 3192 4
  · have he : independentCachedBranchMembers8420.erase 3192=independentCachedBranchMembers8416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8416
  · have he : independentCachedBranchMembers8420.filter (independentCachedEdge 3192)=independentCachedBranchMembers8419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8419
def independentCachedBranchMembers8421 : Finset ℕ := ([48,192,1582,1650,1652,1752,2680,2702,2770,2772,3130,3132,3174,3222,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8421 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8421 4 (fun x => (if x<2770 then (if x<1652 then (if x<1582 then (if x<192 then 0 else 0) else (if x<1650 then 1 else 1)) else (if x<2680 then (if x<1752 then 2 else 2) else (if x<2702 then 2 else 1))) else (if x<3174 then (if x<3130 then (if x<2772 then 1 else 2) else (if x<3132 then 0 else 3)) else (if x<3274 then (if x<3222 then 3 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8422 : Finset ℕ := ([48,132,192,222,1582,1590,1642,1650,1652,1690,1692,1734,1752,2618,2662,2680,2702,2710,2762,2764,2770,2772,3130,3132,3174,3192,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8422 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8422 2710 4
  · have he : independentCachedBranchMembers8422.erase 2710=independentCachedBranchMembers8420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8420
  · have he : independentCachedBranchMembers8422.filter (independentCachedEdge 2710)=independentCachedBranchMembers8421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8421
def independentCachedBranchMembers8423 : Finset ℕ := ([132,222,1642,1650,1690,1752,2618,2680,2762,2770,3132,3174,3214,3222,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8423 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8423 4 (fun x => (if x<2762 then (if x<1690 then (if x<1642 then (if x<222 then 0 else 0) else (if x<1650 then 1 else 2)) else (if x<2618 then (if x<1752 then 1 else 2) else (if x<2680 then 1 else 2))) else (if x<3214 then (if x<3132 then (if x<2770 then 1 else 2) else (if x<3174 then 3 else 3)) else (if x<3276 then (if x<3222 then 0 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8424 : Finset ℕ := ([48,132,192,222,1582,1590,1642,1650,1652,1690,1692,1734,1752,2618,2620,2662,2680,2702,2710,2762,2764,2770,2772,3130,3132,3174,3192,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8424 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8424 2620 4
  · have he : independentCachedBranchMembers8424.erase 2620=independentCachedBranchMembers8422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8422
  · have he : independentCachedBranchMembers8424.filter (independentCachedEdge 2620)=independentCachedBranchMembers8423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8423
def independentCachedBranchMembers8425 : Finset ℕ := ([48,132,192,222,1582,1642,1652,1690,2618,2702,2762,2772,3130,3214,3274,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8425 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8425 4 (fun x => (if x<2618 then (if x<1582 then (if x<192 then (if x<132 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1652 then (if x<1642 then 2 else 3) else (if x<1690 then 2 else 3))) else (if x<3130 then (if x<2762 then (if x<2702 then 0 else 0) else (if x<2772 then 1 else 1)) else (if x<3274 then (if x<3214 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8426 : Finset ℕ := ([48,132,192,222,1582,1590,1642,1644,1650,1652,1690,1692,1734,1752,2618,2620,2662,2680,2702,2710,2762,2764,2770,2772,3130,3132,3174,3192,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8426 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8426 1644 4
  · have he : independentCachedBranchMembers8426.erase 1644=independentCachedBranchMembers8424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8424
  · have he : independentCachedBranchMembers8426.filter (independentCachedEdge 1644)=independentCachedBranchMembers8425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8425
def independentCachedBranchMembers8427 : Finset ℕ := ([132,192,1582,1590,1642,1650,1692,1752,2618,2662,2764,2772,3130,3174,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8427 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8427 4 (fun x => (if x<2618 then (if x<1642 then (if x<1582 then (if x<192 then 0 else 1) else (if x<1590 then 1 else 2)) else (if x<1692 then (if x<1650 then 0 else 3) else (if x<1752 then 2 else 3))) else (if x<3130 then (if x<2764 then (if x<2662 then 0 else 2) else (if x<2772 then 2 else 1)) else (if x<3276 then (if x<3174 then 1 else 3) else (if x<3284 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8428 : Finset ℕ := ([48,130,132,192,222,1582,1590,1642,1644,1650,1652,1690,1692,1734,1752,2618,2620,2662,2680,2702,2710,2762,2764,2770,2772,3130,3132,3174,3192,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8428 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8428 130 4
  · have he : independentCachedBranchMembers8428.erase 130=independentCachedBranchMembers8426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8426
  · have he : independentCachedBranchMembers8428.filter (independentCachedEdge 130)=independentCachedBranchMembers8427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8427
def independentCachedBranchMembers8429 : Finset ℕ := ([48,222,1590,1650,1652,1690,1692,1752,2662,2702,2762,2764,3174,3214,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8429 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8429 4 (fun x => (if x<2662 then (if x<1652 then (if x<1590 then (if x<222 then 0 else 1) else (if x<1650 then 0 else 2)) else (if x<1692 then (if x<1690 then 3 else 1) else (if x<1752 then 3 else 2))) else (if x<3174 then (if x<2762 then (if x<2702 then 2 else 1) else (if x<2764 then 0 else 2)) else (if x<3274 then (if x<3214 then 3 else 3) else (if x<3276 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8430 : Finset ℕ := ([40,48,130,132,192,222,1582,1590,1642,1644,1650,1652,1690,1692,1734,1752,2618,2620,2662,2680,2702,2710,2762,2764,2770,2772,3130,3132,3174,3192,3214,3222,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound8430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8430 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8430 40 4
  · have he : independentCachedBranchMembers8430.erase 40=independentCachedBranchMembers8428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8428
  · have he : independentCachedBranchMembers8430.filter (independentCachedEdge 40)=independentCachedBranchMembers8429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8429
def independentCachedBranchMembers8431 : Finset ℕ := ([12,18,40,48,72,80,130,132,160,190,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2560,2590,2618,2620,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8431 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8431 160 5
  · have he : independentCachedBranchMembers8431.erase 160=independentCachedBranchMembers8407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8407
  · have he : independentCachedBranchMembers8431.filter (independentCachedEdge 160)=independentCachedBranchMembers8430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8430
def independentCachedBranchMembers8432 : Finset ℕ := ([80,250,1582,1614,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8432 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8432 5 (fun x => (if x<2662 then (if x<1702 then (if x<1614 then (if x<250 then 0 else (if x<1582 then 0 else 1)) else (if x<1650 then 2 else (if x<1690 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1734 then 3 else 1)) else (if x<2618 then (if x<1764 then 0 else 3) else (if x<2650 then 1 else 0)))) else (if x<3162 then (if x<2764 then (if x<2680 then 1 else (if x<2702 then 4 else 1)) else (if x<2800 then (if x<2770 then 4 else 1) else (if x<3130 then 0 else 3))) else (if x<3214 then (if x<3174 then 2 else (if x<3192 then 2 else 0)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8433 : Finset ℕ := ([250,1582,1614,1690,1720,1752,2662,2770,2800,3174,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8433 4 (fun x => (if x<2662 then (if x<1690 then (if x<1582 then 0 else (if x<1614 then 1 else 2)) else (if x<1720 then 0 else (if x<1752 then 1 else 2))) else (if x<3174 then (if x<2770 then 1 else (if x<2800 then 0 else 1)) else (if x<3250 then 2 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8434 : Finset ℕ := ([80,132,250,1582,1614,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8434 132 4
  · have he : independentCachedBranchMembers8434.erase 132=independentCachedBranchMembers8432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8432
  · have he : independentCachedBranchMembers8434.filter (independentCachedEdge 132)=independentCachedBranchMembers8433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8433
def independentCachedBranchMembers8435 : Finset ℕ := ([80,1582,1690,1702,1752,1764,2650,2662,2770,3162,3174,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8435 4 (fun x => (if x<2650 then (if x<1702 then (if x<1582 then 0 else (if x<1690 then 0 else 1)) else (if x<1752 then 1 else (if x<1764 then 2 else 2))) else (if x<3162 then (if x<2662 then 1 else (if x<2770 then 1 else 0)) else (if x<3174 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8436 : Finset ℕ := ([48,80,132,250,1582,1614,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8436 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8436 48 4
  · have he : independentCachedBranchMembers8436.erase 48=independentCachedBranchMembers8434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8434
  · have he : independentCachedBranchMembers8436.filter (independentCachedEdge 48)=independentCachedBranchMembers8435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8435
def independentCachedBranchMembers8437 : Finset ℕ := ([132,1614,1702,1720,1764,2618,2662,2680,2702,2764,2770,3162,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8437 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8437 4 (fun x => (if x<2680 then (if x<1720 then (if x<1614 then 0 else (if x<1702 then 1 else 0)) else (if x<2618 then (if x<1764 then 2 else 1) else (if x<2662 then 2 else 1))) else (if x<3162 then (if x<2764 then (if x<2702 then 0 else 3) else (if x<2770 then 1 else 3)) else (if x<3250 then (if x<3244 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8438 : Finset ℕ := ([1702,1764,2662,2770,3162,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8438 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8438 3 (fun x => (if x<2770 then (if x<1764 then 0 else (if x<2662 then 1 else 0)) else (if x<3162 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8439 : Finset ℕ := ([48,132,1614,1702,1720,1764,2618,2662,2680,2702,2764,2770,3162,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8439 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8439 48 3
  · have he : independentCachedBranchMembers8439.erase 48=independentCachedBranchMembers8437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8437
  · have he : independentCachedBranchMembers8439.filter (independentCachedEdge 48)=independentCachedBranchMembers8438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8438
def independentCachedBranchMembers8440 : Finset ℕ := ([48,80,132,250,1582,1614,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8440 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8440 3282 4
  · have he : independentCachedBranchMembers8440.erase 3282=independentCachedBranchMembers8436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8436
  · have he : independentCachedBranchMembers8440.filter (independentCachedEdge 3282)=independentCachedBranchMembers8439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8439
def independentCachedBranchMembers8441 : Finset ℕ := ([250,1582,1690,1702,1720,2650,2662,2680,2764,2770,2800,3130,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8441 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8441 4 (fun x => (if x<2680 then (if x<1702 then (if x<1582 then 0 else (if x<1690 then 1 else 0)) else (if x<2650 then (if x<1720 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3130 then (if x<2770 then (if x<2764 then 2 else 3) else (if x<2800 then 3 else 1)) else (if x<3244 then (if x<3214 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8442 : Finset ℕ := ([1690,1720,2662,2764,3130,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8442 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8442 3 (fun x => (if x<2764 then (if x<1720 then 0 else (if x<2662 then 1 else 0)) else (if x<3130 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8443 : Finset ℕ := ([80,250,1582,1690,1702,1720,2650,2662,2680,2764,2770,2800,3130,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8443 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8443 80 3
  · have he : independentCachedBranchMembers8443.erase 80=independentCachedBranchMembers8441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8441
  · have he : independentCachedBranchMembers8443.filter (independentCachedEdge 80)=independentCachedBranchMembers8442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8442
def independentCachedBranchMembers8444 : Finset ℕ := ([48,80,132,250,1582,1614,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8444 3276 4
  · have he : independentCachedBranchMembers8444.erase 3276=independentCachedBranchMembers8440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8440
  · have he : independentCachedBranchMembers8444.filter (independentCachedEdge 3276)=independentCachedBranchMembers8443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8443
def independentCachedBranchMembers8445 : Finset ℕ := ([80,132,1582,1734,1752,1764,2618,2764,2770,2800,3162,3174,3192,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8445 4 (fun x => (if x<2770 then (if x<1752 then (if x<1582 then (if x<132 then 0 else 0) else (if x<1734 then 1 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2764 then 1 else 2))) else (if x<3192 then (if x<3162 then (if x<2800 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3244 then (if x<3214 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8446 : Finset ℕ := ([48,80,132,250,1582,1614,1650,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2702,2738,2764,2770,2800,3130,3162,3174,3192,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8446 2738 4
  · have he : independentCachedBranchMembers8446.erase 2738=independentCachedBranchMembers8444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8444
  · have he : independentCachedBranchMembers8446.filter (independentCachedEdge 2738)=independentCachedBranchMembers8445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8445
def independentCachedBranchMembers8447 : Finset ℕ := ([48,250,1614,1690,1734,1752,2650,2702,2764,2770,3130,3174,3192,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8447 4 (fun x => (if x<2764 then (if x<1734 then (if x<1614 then (if x<250 then 0 else 0) else (if x<1690 then 1 else 1)) else (if x<2650 then (if x<1752 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3192 then (if x<3130 then (if x<2770 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
