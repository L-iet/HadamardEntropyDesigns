/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch112
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6400 : Finset ℕ := ([246,1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6400 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6400 5 (fun x => (if x<2716 then (if x<1702 then (if x<1642 then (if x<1582 then 0 else (if x<1622 then 1 else 0)) else (if x<1652 then 2 else (if x<1690 then 1 else 2))) else (if x<2614 then (if x<1720 then 0 else (if x<1762 then 1 else 1)) else (if x<2668 then (if x<2638 then 0 else 3) else (if x<2674 then 2 else 3)))) else (if x<3174 then (if x<2788 then (if x<2758 then 2 else (if x<2776 then 0 else 3)) else (if x<3132 then 3 else (if x<3162 then 1 else 3))) else (if x<3252 then (if x<3222 then 0 else (if x<3242 then 0 else 1)) else (if x<3282 then (if x<3276 then 4 else 3) else (if x<3312 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6401 : Finset ℕ := ([1622,1652,1702,1762,2614,2674,2758,2788,3132,3162,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6401 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6401 4 (fun x => (if x<2758 then (if x<1762 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then 1 else (if x<2674 then 0 else 1))) else (if x<3162 then (if x<2788 then 0 else (if x<3132 then 1 else 2)) else (if x<3242 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6402 : Finset ℕ := ([144,246,1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6402 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6402 144 4
  · have he : independentCachedBranchMembers6402.erase 144=independentCachedBranchMembers6400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6400
  · have he : independentCachedBranchMembers6402.filter (independentCachedEdge 144)=independentCachedBranchMembers6401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6401
def independentCachedBranchMembers6403 : Finset ℕ := ([1582,1652,1690,1702,2614,2668,2776,2788,3222,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6403 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6403 4 (fun x => (if x<2776 then (if x<1702 then (if x<1652 then 0 else (if x<1690 then 0 else 1)) else (if x<2614 then 1 else (if x<2668 then 0 else 0))) else (if x<3242 then (if x<2788 then 1 else (if x<3222 then 1 else 2)) else (if x<3276 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6404 : Finset ℕ := ([66,144,246,1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6404 66 4
  · have he : independentCachedBranchMembers6404.erase 66=independentCachedBranchMembers6402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6402
  · have he : independentCachedBranchMembers6404.filter (independentCachedEdge 66)=independentCachedBranchMembers6403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6403
def independentCachedBranchMembers6405 : Finset ℕ := ([1622,1642,1720,1762,2638,2674,2716,2758,3222,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6405 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6405 4 (fun x => (if x<2716 then (if x<1762 then (if x<1642 then 0 else (if x<1720 then 0 else 1)) else (if x<2638 then 1 else (if x<2674 then 0 else 0))) else (if x<3242 then (if x<2758 then 1 else (if x<3222 then 1 else 2)) else (if x<3276 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6406 : Finset ℕ := ([36,66,144,246,1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6406 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6406 36 4
  · have he : independentCachedBranchMembers6406.erase 36=independentCachedBranchMembers6404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6404
  · have he : independentCachedBranchMembers6406.filter (independentCachedEdge 36)=independentCachedBranchMembers6405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6405
def independentCachedBranchMembers6407 : Finset ℕ := ([36,66,144,246,1582,1622,1690,1762,2614,2638,2716,2788,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6407 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6407 4 (fun x => (if x<2614 then (if x<1582 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3132 then (if x<2716 then (if x<2638 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6408 : Finset ℕ := ([36,66,144,246,1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6408 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6408 3192 4
  · have he : independentCachedBranchMembers6408.erase 3192=independentCachedBranchMembers6406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6406
  · have he : independentCachedBranchMembers6408.filter (independentCachedEdge 3192)=independentCachedBranchMembers6407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6407
def independentCachedBranchMembers6409 : Finset ℕ := ([36,66,144,246,1642,1652,1702,1720,2668,2674,2758,2776,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6409 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6409 4 (fun x => (if x<2668 then (if x<1642 then (if x<144 then (if x<66 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3132 then (if x<2758 then (if x<2674 then 2 else 2) else (if x<2776 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6410 : Finset ℕ := ([36,66,144,246,1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6410 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6410 3102 4
  · have he : independentCachedBranchMembers6410.erase 3102=independentCachedBranchMembers6408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6408
  · have he : independentCachedBranchMembers6410.filter (independentCachedEdge 3102)=independentCachedBranchMembers6409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6409
def independentCachedBranchMembers6411 : Finset ℕ := ([1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788] : List ℕ).toFinset
theorem independentCachedBranchBound6411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6411 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6411 4 (fun x => (if x<2614 then (if x<1690 then (if x<1642 then (if x<1622 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1762 then 1 else 0))) else (if x<2716 then (if x<2668 then (if x<2638 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2776 then (if x<2758 then 2 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6412 : Finset ℕ := ([36,66,144,246,1582,1622,1642,1652,1690,1702,1720,1762,2614,2638,2668,2674,2716,2758,2776,2788,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6412 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6412 3072 4
  · have he : independentCachedBranchMembers6412.erase 3072=independentCachedBranchMembers6410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6410
  · have he : independentCachedBranchMembers6412.filter (independentCachedEdge 3072)=independentCachedBranchMembers6411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6411
def independentCachedBranchMembers6413 : Finset ℕ := ([36,48,66,72,132,144,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6413 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6413 2764 5
  · have he : independentCachedBranchMembers6413.erase 2764=independentCachedBranchMembers6399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6399
  · have he : independentCachedBranchMembers6413.filter (independentCachedEdge 2764)=independentCachedBranchMembers6412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6412
def independentCachedBranchMembers6414 : Finset ℕ := ([48,252,1582,1594,1652,1708,1714,1720,1762,1768,2614,2620,2668,2674,2730,2740,2788,2800,3126,3132,3174,3192,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6414 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6414 5 (fun x => (if x<2674 then (if x<1714 then (if x<1594 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1652 then 2 else (if x<1708 then 0 else 2))) else (if x<1768 then (if x<1720 then 1 else (if x<1762 then 0 else 2)) else (if x<2620 then (if x<2614 then 1 else 1) else (if x<2668 then 0 else 1)))) else (if x<3132 then (if x<2788 then (if x<2730 then 2 else (if x<2740 then 1 else 3)) else (if x<2800 then 2 else (if x<3126 then 0 else 3))) else (if x<3242 then (if x<3174 then 4 else (if x<3192 then 4 else 0)) else (if x<3300 then (if x<3252 then 4 else 0) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6415 : Finset ℕ := ([48,252,1582,1708,1714,1762,2620,2668,2674,2800,3132,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6415 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6415 4 (fun x => (if x<2620 then (if x<1708 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1714 then 2 else (if x<1762 then 1 else 2))) else (if x<2800 then (if x<2668 then 0 else (if x<2674 then 1 else 2)) else (if x<3132 then 0 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6416 : Finset ℕ := ([48,252,1582,1594,1652,1702,1708,1714,1720,1762,1768,2614,2620,2668,2674,2730,2740,2788,2800,3126,3132,3174,3192,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6416 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6416 1702 4
  · have he : independentCachedBranchMembers6416.erase 1702=independentCachedBranchMembers6414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6414
  · have he : independentCachedBranchMembers6416.filter (independentCachedEdge 1702)=independentCachedBranchMembers6415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6415
def independentCachedBranchMembers6417 : Finset ℕ := ([252,1582,1594,1708,1720,1768,2620,2668,2730,3132,3192,3242] : List ℕ).toFinset
theorem independentCachedBranchBound6417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6417 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6417 4 (fun x => (if x<2620 then (if x<1708 then (if x<1582 then 0 else (if x<1594 then 1 else 2)) else (if x<1720 then 0 else (if x<1768 then 1 else 2))) else (if x<3132 then (if x<2668 then 0 else (if x<2730 then 3 else 1)) else (if x<3192 then 3 else (if x<3242 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6418 : Finset ℕ := ([48,246,252,1582,1594,1652,1702,1708,1714,1720,1762,1768,2614,2620,2668,2674,2730,2740,2788,2800,3126,3132,3174,3192,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6418 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6418 246 4
  · have he : independentCachedBranchMembers6418.erase 246=independentCachedBranchMembers6416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6416
  · have he : independentCachedBranchMembers6418.filter (independentCachedEdge 246)=independentCachedBranchMembers6417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6417
def independentCachedBranchMembers6419 : Finset ℕ := ([48,1594,1714,1720,1762,1768,2674,2730,2800,3192,3242,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6419 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6419 4 (fun x => (if x<2674 then (if x<1720 then (if x<1594 then 0 else (if x<1714 then 0 else 1)) else (if x<1762 then 2 else (if x<1768 then 2 else 1))) else (if x<3192 then (if x<2730 then 0 else (if x<2800 then 1 else 1)) else (if x<3242 then 0 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6420 : Finset ℕ := ([36,48,246,252,1582,1594,1652,1702,1708,1714,1720,1762,1768,2614,2620,2668,2674,2730,2740,2788,2800,3126,3132,3174,3192,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6420 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6420 36 4
  · have he : independentCachedBranchMembers6420.erase 36=independentCachedBranchMembers6418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6418
  · have he : independentCachedBranchMembers6420.filter (independentCachedEdge 36)=independentCachedBranchMembers6419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6419
def independentCachedBranchMembers6421 : Finset ℕ := ([252,1582,1702,1720,1768,2620,2668,2674,2730,2740,2788,3126,3174,3192,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6421 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6421 4 (fun x => (if x<2674 then (if x<1720 then (if x<1582 then 0 else (if x<1702 then 1 else 2)) else (if x<2620 then (if x<1768 then 0 else 1) else (if x<2668 then 0 else 1))) else (if x<3126 then (if x<2740 then (if x<2730 then 3 else 1) else (if x<2788 then 2 else 3)) else (if x<3192 then (if x<3174 then 2 else 3) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6422 : Finset ℕ := ([1720,1768,2674,2730,3192,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6422 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6422 3 (fun x => (if x<2730 then (if x<1768 then 0 else (if x<2674 then 1 else 2)) else (if x<3192 then 0 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6423 : Finset ℕ := ([36,252,1582,1702,1720,1768,2620,2668,2674,2730,2740,2788,3126,3174,3192,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6423 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6423 36 3
  · have he : independentCachedBranchMembers6423.erase 36=independentCachedBranchMembers6421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6421
  · have he : independentCachedBranchMembers6423.filter (independentCachedEdge 36)=independentCachedBranchMembers6422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6422
def independentCachedBranchMembers6424 : Finset ℕ := ([36,48,246,252,1582,1594,1652,1702,1708,1714,1720,1762,1768,2614,2620,2668,2674,2730,2740,2788,2800,3126,3132,3174,3186,3192,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6424 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6424 3186 4
  · have he : independentCachedBranchMembers6424.erase 3186=independentCachedBranchMembers6420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6420
  · have he : independentCachedBranchMembers6424.filter (independentCachedEdge 3186)=independentCachedBranchMembers6423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6423
def independentCachedBranchMembers6425 : Finset ℕ := ([246,1594,1702,1720,1762,2614,2668,2674,2730,2740,2800,3132,3174,3192,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6425 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6425 4 (fun x => (if x<2674 then (if x<1720 then (if x<1594 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then (if x<1762 then 2 else 1) else (if x<2668 then 0 else 3))) else (if x<3132 then (if x<2740 then (if x<2730 then 1 else 1) else (if x<2800 then 2 else 3)) else (if x<3192 then (if x<3174 then 2 else 0) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6426 : Finset ℕ := ([1702,1762,2668,2730,3174,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6426 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6426 3 (fun x => (if x<2730 then (if x<1762 then 0 else (if x<2668 then 1 else 2)) else (if x<3174 then 0 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6427 : Finset ℕ := ([48,246,1594,1702,1720,1762,2614,2668,2674,2730,2740,2800,3132,3174,3192,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6427 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6427 48 3
  · have he : independentCachedBranchMembers6427.erase 48=independentCachedBranchMembers6425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6425
  · have he : independentCachedBranchMembers6427.filter (independentCachedEdge 48)=independentCachedBranchMembers6426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6426
def independentCachedBranchMembers6428 : Finset ℕ := ([36,48,246,252,1582,1594,1652,1702,1708,1714,1720,1762,1768,2614,2620,2668,2674,2730,2740,2788,2800,3126,3132,3174,3180,3186,3192,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6428 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6428 3180 4
  · have he : independentCachedBranchMembers6428.erase 3180=independentCachedBranchMembers6424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6424
  · have he : independentCachedBranchMembers6428.filter (independentCachedEdge 3180)=independentCachedBranchMembers6427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6427
def independentCachedBranchMembers6429 : Finset ℕ := ([36,48,246,252,1582,1594,1762,1768,2614,2620,2788,2800,3126,3132,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6429 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6429 4 (fun x => (if x<2614 then (if x<1582 then (if x<246 then (if x<48 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1762 then (if x<1594 then 2 else 3) else (if x<1768 then 2 else 3))) else (if x<3126 then (if x<2788 then (if x<2620 then 0 else 1) else (if x<2800 then 0 else 1)) else (if x<3300 then (if x<3132 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6430 : Finset ℕ := ([36,48,246,252,1582,1594,1642,1652,1702,1708,1714,1720,1762,1768,2614,2620,2668,2674,2730,2740,2788,2800,3126,3132,3174,3180,3186,3192,3242,3252,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6430 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6430 1642 4
  · have he : independentCachedBranchMembers6430.erase 1642=independentCachedBranchMembers6428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6428
  · have he : independentCachedBranchMembers6430.filter (independentCachedEdge 1642)=independentCachedBranchMembers6429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6429
def independentCachedBranchMembers6431 : Finset ℕ := ([36,48,66,72,132,144,222,246,252,1582,1594,1622,1628,1642,1652,1678,1690,1702,1708,1714,1720,1738,1748,1762,1768,2614,2620,2638,2650,2668,2674,2710,2716,2730,2740,2758,2764,2770,2776,2788,2800,3072,3102,3126,3132,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3270,3276,3282,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6431 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6431 222 5
  · have he : independentCachedBranchMembers6431.erase 222=independentCachedBranchMembers6413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6413
  · have he : independentCachedBranchMembers6431.filter (independentCachedEdge 222)=independentCachedBranchMembers6430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6430
end EntropyDesigns.QuadraticRefinement
