/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch10
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1408 : Finset ℕ := ([12,48,1652,1692,1734,1740,1776,2614,2620,2650,2668,2702,2738,2772,2792,3102,3150,3186,3192,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1408 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1408 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1408 5 (fun x => (if x<2668 then (if x<1740 then (if x<1652 then (if x<48 then 0 else 0) else (if x<1692 then 1 else (if x<1734 then 1 else 1))) else (if x<2614 then (if x<1776 then 0 else 0) else (if x<2620 then 2 else (if x<2650 then 1 else 2)))) else (if x<3102 then (if x<2738 then (if x<2702 then 2 else 0) else (if x<2772 then 0 else (if x<2792 then 1 else 3))) else (if x<3192 then (if x<3150 then 3 else (if x<3186 then 0 else 0)) else (if x<3244 then 3 else (if x<3274 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1409 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1409 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1409 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1409 1748 5
  · have he : independentCachedBranchMembers1409.erase 1748=independentCachedBranchMembers1407 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1407
  · have he : independentCachedBranchMembers1409.filter (independentCachedEdge 1748)=independentCachedBranchMembers1408 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1408
def independentCachedBranchMembers1410 : Finset ℕ := ([192,252,1652,1692,1734,1740,1776,2614,2620,2650,2668,2702,2738,2772,2792,3130,3164,3252,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1410 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1410 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1410 5 (fun x => (if x<2668 then (if x<1740 then (if x<1652 then (if x<252 then 0 else 0) else (if x<1692 then 1 else (if x<1734 then 1 else 1))) else (if x<2614 then (if x<1776 then 0 else 0) else (if x<2620 then 2 else (if x<2650 then 1 else 2)))) else (if x<3130 then (if x<2738 then (if x<2702 then 2 else 1) else (if x<2772 then 3 else (if x<2792 then 0 else 0))) else (if x<3282 then (if x<3164 then 3 else (if x<3252 then 3 else 3)) else (if x<3288 then 3 else (if x<3300 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1411 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1411 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1411 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1411 1678 5
  · have he : independentCachedBranchMembers1411.erase 1678=independentCachedBranchMembers1409 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1409
  · have he : independentCachedBranchMembers1411.filter (independentCachedEdge 1678)=independentCachedBranchMembers1410 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1410
def independentCachedBranchMembers1412 : Finset ℕ := ([48,192,1596,1652,1714,1740,1768,2614,2650,2668,2702,2716,2758,2772,2800,3102,3130,3186,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1412 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1412 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1412 5 (fun x => (if x<2702 then (if x<1740 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1652 then 0 else (if x<1714 then 1 else 1))) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2650 then 0 else (if x<2668 then 2 else 1)))) else (if x<3102 then (if x<2758 then (if x<2716 then 2 else 3) else (if x<2772 then 0 else (if x<2800 then 2 else 1))) else (if x<3252 then (if x<3130 then 3 else (if x<3186 then 0 else 3)) else (if x<3274 then 3 else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1413 : Finset ℕ := ([12,48,192,252,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1413 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1413 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1413 1644 5
  · have he : independentCachedBranchMembers1413.erase 1644=independentCachedBranchMembers1411 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1411
  · have he : independentCachedBranchMembers1413.filter (independentCachedEdge 1644)=independentCachedBranchMembers1412 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1412
def independentCachedBranchMembers1414 : Finset ℕ := ([12,252,1596,1652,1714,1740,1768,2614,2650,2668,2702,2716,2758,2772,2800,3150,3164,3192,3244,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1414 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1414 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1414 5 (fun x => (if x<2702 then (if x<1740 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1652 then 0 else (if x<1714 then 1 else 1))) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2650 then 1 else (if x<2668 then 2 else 0)))) else (if x<3150 then (if x<2758 then (if x<2716 then 2 else 0) else (if x<2772 then 3 else (if x<2800 then 2 else 1))) else (if x<3244 then (if x<3164 then 3 else (if x<3192 then 0 else 3)) else (if x<3282 then 0 else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1415 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1415 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1415 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1415 1590 5
  · have he : independentCachedBranchMembers1415.erase 1590=independentCachedBranchMembers1413 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1413
  · have he : independentCachedBranchMembers1415.filter (independentCachedEdge 1590)=independentCachedBranchMembers1414 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1414
def independentCachedBranchMembers1416 : Finset ℕ := ([48,192,252,1596,1734,1740,1748,1768,1776,2614,2620,2758,2764,2772,2792,2800,3102,3130,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1416 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1416 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1416 5 (fun x => (if x<2758 then (if x<1740 then (if x<252 then (if x<192 then 0 else 0) else (if x<1596 then 0 else (if x<1734 then 0 else 1))) else (if x<1776 then (if x<1748 then 0 else (if x<1768 then 2 else 1)) else (if x<2614 then 0 else (if x<2620 then 3 else 4)))) else (if x<3102 then (if x<2772 then (if x<2764 then 2 else 1) else (if x<2792 then 3 else (if x<2800 then 4 else 2))) else (if x<3282 then (if x<3130 then 4 else (if x<3274 then 3 else 1)) else (if x<3288 then 2 else (if x<3300 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1417 : Finset ℕ := ([252,1596,1740,1768,2614,2758,2772,2800,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1417 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1417 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1417 4 (fun x => (if x<2758 then (if x<1740 then (if x<1596 then 0 else 0) else (if x<1768 then 0 else (if x<2614 then 1 else 1))) else (if x<2800 then (if x<2772 then 2 else 3) else (if x<3282 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1418 : Finset ℕ := ([48,192,252,1590,1596,1734,1740,1748,1768,1776,2614,2620,2758,2764,2772,2792,2800,3102,3130,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1418 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1418 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1418 1590 4
  · have he : independentCachedBranchMembers1418.erase 1590=independentCachedBranchMembers1416 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1416
  · have he : independentCachedBranchMembers1418.filter (independentCachedEdge 1590)=independentCachedBranchMembers1417 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1417
def independentCachedBranchMembers1419 : Finset ℕ := ([1590,1734,1748,1768,2614,2758,2772,2792,3130,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1419 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1419 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1419 4 (fun x => (if x<2772 then (if x<1768 then (if x<1734 then 0 else (if x<1748 then 0 else 1)) else (if x<2614 then 1 else (if x<2758 then 2 else 2))) else (if x<3274 then (if x<2792 then 3 else (if x<3130 then 3 else 0)) else (if x<3288 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1420 : Finset ℕ := ([12,48,192,252,1590,1596,1734,1740,1748,1768,1776,2614,2620,2758,2764,2772,2792,2800,3102,3130,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1420 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1420 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1420 12 4
  · have he : independentCachedBranchMembers1420.erase 12=independentCachedBranchMembers1418 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1418
  · have he : independentCachedBranchMembers1420.filter (independentCachedEdge 12)=independentCachedBranchMembers1419 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1419
def independentCachedBranchMembers1421 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3226,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1421 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1421 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1421 3226 5
  · have he : independentCachedBranchMembers1421.erase 3226=independentCachedBranchMembers1415 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1415
  · have he : independentCachedBranchMembers1421.filter (independentCachedEdge 3226)=independentCachedBranchMembers1420 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1420
def independentCachedBranchMembers1422 : Finset ℕ := ([12,48,252,1596,1678,1692,1714,1740,1776,2620,2668,2702,2716,2738,2764,2800,3102,3150,3164,3186,3244,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1422 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1422 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1422 5 (fun x => (if x<2702 then (if x<1692 then (if x<252 then (if x<48 then 0 else 0) else (if x<1596 then 0 else (if x<1678 then 0 else 1))) else (if x<1776 then (if x<1714 then 2 else (if x<1740 then 1 else 0)) else (if x<2620 then 0 else (if x<2668 then 2 else 3)))) else (if x<3102 then (if x<2738 then (if x<2716 then 2 else 3) else (if x<2764 then 4 else (if x<2800 then 1 else 1))) else (if x<3186 then (if x<3150 then 2 else (if x<3164 then 1 else 3)) else (if x<3244 then 1 else (if x<3282 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1423 : Finset ℕ := ([48,1596,1714,1740,2668,2702,2716,2800,3102,3186] : List ℕ).toFinset
theorem independentCachedBranchBound1423 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1423 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1423 4 (fun x => (if x<2702 then (if x<1714 then (if x<1596 then 0 else 0) else (if x<1740 then 0 else (if x<2668 then 1 else 1))) else (if x<2800 then (if x<2716 then 1 else 2) else (if x<3102 then 2 else (if x<3186 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1424 : Finset ℕ := ([12,48,252,1596,1644,1678,1692,1714,1740,1776,2620,2668,2702,2716,2738,2764,2800,3102,3150,3164,3186,3244,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1424 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1424 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1424 1644 4
  · have he : independentCachedBranchMembers1424.erase 1644=independentCachedBranchMembers1422 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1422
  · have he : independentCachedBranchMembers1424.filter (independentCachedEdge 1644)=independentCachedBranchMembers1423 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1423
def independentCachedBranchMembers1425 : Finset ℕ := ([1644,1678,1692,1714,2668,2702,2716,2738,3150,3164,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound1425 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1425 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1425 4 (fun x => (if x<2716 then (if x<1714 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2668 then 1 else (if x<2702 then 2 else 2))) else (if x<3164 then (if x<2738 then 3 else (if x<3150 then 3 else 0)) else (if x<3186 then 1 else (if x<3244 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1426 : Finset ℕ := ([12,48,192,252,1596,1644,1678,1692,1714,1740,1776,2620,2668,2702,2716,2738,2764,2800,3102,3150,3164,3186,3244,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1426 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1426 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1426 192 4
  · have he : independentCachedBranchMembers1426.erase 192=independentCachedBranchMembers1424 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1424
  · have he : independentCachedBranchMembers1426.filter (independentCachedEdge 192)=independentCachedBranchMembers1425 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1425
def independentCachedBranchMembers1427 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3158,3164,3186,3192,3226,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1427 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1427 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1427 3158 5
  · have he : independentCachedBranchMembers1427.erase 3158=independentCachedBranchMembers1421 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1421
  · have he : independentCachedBranchMembers1427.filter (independentCachedEdge 3158)=independentCachedBranchMembers1426 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1426
def independentCachedBranchMembers1428 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1692,1734,1740,1776,2702,2738,2772,2792,3102,3150,3186,3192,3252,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1428 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1428 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1428 5 (fun x => (if x<2702 then (if x<1626 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1590 then 0 else (if x<1596 then 1 else 0))) else (if x<1734 then (if x<1644 then 1 else (if x<1692 then 1 else 1)) else (if x<1740 then 1 else (if x<1776 then 0 else 0)))) else (if x<3186 then (if x<2792 then (if x<2738 then 2 else (if x<2772 then 2 else 2)) else (if x<3102 then 2 else (if x<3150 then 3 else 4))) else (if x<3282 then (if x<3192 then 3 else (if x<3252 then 4 else 3)) else (if x<3288 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1429 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2668,2702,2716,2730,2738,2758,2764,2772,2792,2800,3102,3130,3150,3158,3164,3186,3192,3226,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1429 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1429 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1429 2730 5
  · have he : independentCachedBranchMembers1429.erase 2730=independentCachedBranchMembers1427 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1427
  · have he : independentCachedBranchMembers1429.filter (independentCachedEdge 2730)=independentCachedBranchMembers1428 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1428
def independentCachedBranchMembers1430 : Finset ℕ := ([12,48,192,252,1596,1626,1678,1714,1740,1748,1768,1776,2614,2668,2716,2758,3102,3130,3164,3192,3244,3252,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1430 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1430 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1430 5 (fun x => (if x<2614 then (if x<1678 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1596 then 0 else (if x<1626 then 0 else 1))) else (if x<1748 then (if x<1714 then 1 else (if x<1740 then 1 else 0)) else (if x<1768 then 1 else (if x<1776 then 1 else 0)))) else (if x<3164 then (if x<2758 then (if x<2668 then 2 else (if x<2716 then 2 else 2)) else (if x<3102 then 2 else (if x<3130 then 3 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3244 then 3 else 3)) else (if x<3274 then 4 else (if x<3282 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1431 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2662,2668,2702,2716,2730,2738,2758,2764,2772,2792,2800,3102,3130,3150,3158,3164,3186,3192,3226,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1431 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1431 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1431 2662 5
  · have he : independentCachedBranchMembers1431.erase 2662=independentCachedBranchMembers1429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1429
  · have he : independentCachedBranchMembers1431.filter (independentCachedEdge 2662)=independentCachedBranchMembers1430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1430
def independentCachedBranchMembers1432 : Finset ℕ := ([12,192,252,1644,1652,1692,1720,1740,1776,2620,2668,2716,2764,2772,2792,2800,3164,3192,3244,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1432 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1432 5 (fun x => (if x<2716 then (if x<1692 then (if x<252 then (if x<192 then 0 else 0) else (if x<1644 then 0 else (if x<1652 then 1 else 2))) else (if x<1776 then (if x<1720 then 1 else (if x<1740 then 2 else 0)) else (if x<2620 then 0 else (if x<2668 then 1 else 3)))) else (if x<3164 then (if x<2772 then (if x<2764 then 3 else 1) else (if x<2792 then 4 else (if x<2800 then 4 else 2))) else (if x<3252 then (if x<3192 then 1 else (if x<3244 then 2 else 1)) else (if x<3288 then 2 else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1433 : Finset ℕ := ([12,1644,1720,1740,1776,2620,2716,2772,2792,3164,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1433 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1433 4 (fun x => (if x<2620 then (if x<1720 then (if x<1644 then 0 else 0) else (if x<1740 then 1 else (if x<1776 then 1 else 0))) else (if x<2792 then (if x<2716 then 2 else (if x<2772 then 1 else 2)) else (if x<3164 then 1 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1434 : Finset ℕ := ([12,192,252,1644,1652,1692,1720,1740,1768,1776,2620,2668,2716,2764,2772,2792,2800,3164,3192,3244,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1434 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1434 1768 4
  · have he : independentCachedBranchMembers1434.erase 1768=independentCachedBranchMembers1432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1432
  · have he : independentCachedBranchMembers1434.filter (independentCachedEdge 1768)=independentCachedBranchMembers1433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1433
def independentCachedBranchMembers1435 : Finset ℕ := ([12,1652,1692,1740,1776,2620,2668,2772,2792,3192,3244] : List ℕ).toFinset
theorem independentCachedBranchBound1435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1435 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1435 4 (fun x => (if x<2620 then (if x<1692 then (if x<1652 then 0 else 1) else (if x<1740 then 0 else (if x<1776 then 1 else 0))) else (if x<2792 then (if x<2668 then 2 else (if x<2772 then 1 else 1)) else (if x<3192 then 2 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1436 : Finset ℕ := ([12,192,252,1644,1652,1692,1720,1740,1748,1768,1776,2620,2668,2716,2764,2772,2792,2800,3164,3192,3244,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1436 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1436 1748 4
  · have he : independentCachedBranchMembers1436.erase 1748=independentCachedBranchMembers1434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1434
  · have he : independentCachedBranchMembers1436.filter (independentCachedEdge 1748)=independentCachedBranchMembers1435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1435
def independentCachedBranchMembers1437 : Finset ℕ := ([1644,1652,1692,1720,2620,2764,2772,2792,2800,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1437 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1437 4 (fun x => (if x<2764 then (if x<1692 then (if x<1652 then 0 else 1) else (if x<1720 then 0 else (if x<2620 then 1 else 0))) else (if x<2800 then (if x<2772 then 0 else (if x<2792 then 2 else 2)) else (if x<3288 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1438 : Finset ℕ := ([12,192,252,1596,1644,1652,1692,1720,1740,1748,1768,1776,2620,2668,2716,2764,2772,2792,2800,3164,3192,3244,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1438 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1438 1596 4
  · have he : independentCachedBranchMembers1438.erase 1596=independentCachedBranchMembers1436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1436
  · have he : independentCachedBranchMembers1438.filter (independentCachedEdge 1596)=independentCachedBranchMembers1437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1437
def independentCachedBranchMembers1439 : Finset ℕ := ([1644,1692,1748,1768,2668,2716,2772,2792,3164,3244,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1439 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1439 4 (fun x => (if x<2772 then (if x<1768 then (if x<1692 then 0 else (if x<1748 then 0 else 1)) else (if x<2668 then 1 else (if x<2716 then 2 else 2))) else (if x<3244 then (if x<2792 then 3 else (if x<3164 then 3 else 0)) else (if x<3288 then 0 else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1440 : Finset ℕ := ([12,48,192,252,1596,1644,1652,1692,1720,1740,1748,1768,1776,2620,2668,2716,2764,2772,2792,2800,3164,3192,3244,3252,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1440 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1440 48 4
  · have he : independentCachedBranchMembers1440.erase 48=independentCachedBranchMembers1438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1438
  · have he : independentCachedBranchMembers1440.filter (independentCachedEdge 48)=independentCachedBranchMembers1439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1439
def independentCachedBranchMembers1441 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2662,2668,2702,2716,2730,2738,2758,2764,2772,2792,2800,3102,3130,3150,3158,3164,3186,3192,3226,3238,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1441 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1441 3238 5
  · have he : independentCachedBranchMembers1441.erase 3238=independentCachedBranchMembers1431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1431
  · have he : independentCachedBranchMembers1441.filter (independentCachedEdge 3238)=independentCachedBranchMembers1440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1440
def independentCachedBranchMembers1442 : Finset ℕ := ([12,48,192,1652,1714,1734,1740,2614,2620,2702,2764,2800,3130,3150,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1442 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1442 5 (fun x => (if x<2620 then (if x<1714 then (if x<192 then (if x<48 then 0 else 0) else (if x<1652 then 0 else 1)) else (if x<1740 then (if x<1734 then 1 else 1) else (if x<2614 then 0 else 2))) else (if x<3130 then (if x<2764 then (if x<2702 then 3 else 2) else (if x<2800 then 3 else 3)) else (if x<3186 then (if x<3150 then 4 else 4) else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1443 : Finset ℕ := ([12,192,1734,1740,2702,2764,3150,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1443 4 (fun x => (if x<2702 then (if x<1734 then (if x<192 then 0 else 0) else (if x<1740 then 1 else 0)) else (if x<3150 then (if x<2764 then 1 else 2) else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1444 : Finset ℕ := ([12,48,192,1652,1714,1734,1740,2614,2620,2702,2764,2800,3130,3150,3186,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1444 3252 4
  · have he : independentCachedBranchMembers1444.erase 3252=independentCachedBranchMembers1442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1442
  · have he : independentCachedBranchMembers1444.filter (independentCachedEdge 3252)=independentCachedBranchMembers1443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1443
def independentCachedBranchMembers1445 : Finset ℕ := ([12,192,1714,1740,2614,2764,3130,3186] : List ℕ).toFinset
theorem independentCachedBranchBound1445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1445 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1445 4 (fun x => (if x<2614 then (if x<1714 then (if x<192 then 0 else 0) else (if x<1740 then 1 else 0)) else (if x<3130 then (if x<2764 then 1 else 2) else (if x<3186 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1446 : Finset ℕ := ([12,48,192,1652,1714,1734,1740,2614,2620,2702,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1446 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1446 3192 4
  · have he : independentCachedBranchMembers1446.erase 3192=independentCachedBranchMembers1444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1444
  · have he : independentCachedBranchMembers1446.filter (independentCachedEdge 3192)=independentCachedBranchMembers1445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1445
def independentCachedBranchMembers1447 : Finset ℕ := ([1652,1714,2614,2620,2764,2800,3130,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1447 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1447 4 (fun x => (if x<2764 then (if x<2614 then (if x<1714 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<3130 then (if x<2800 then 1 else 0) else (if x<3274 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1448 : Finset ℕ := ([12,48,192,1652,1714,1734,1740,1776,2614,2620,2702,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1448 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1448 1776 4
  · have he : independentCachedBranchMembers1448.erase 1776=independentCachedBranchMembers1446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1446
  · have he : independentCachedBranchMembers1448.filter (independentCachedEdge 1776)=independentCachedBranchMembers1447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1447
def independentCachedBranchMembers1449 : Finset ℕ := ([1652,1734,2620,2702,2764,2800,3150,3186] : List ℕ).toFinset
theorem independentCachedBranchBound1449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1449 4 (fun x => (if x<2764 then (if x<2620 then (if x<1734 then 0 else 0) else (if x<2702 then 0 else 0)) else (if x<3150 then (if x<2800 then 1 else 1) else (if x<3186 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1450 : Finset ℕ := ([12,48,192,1596,1652,1714,1734,1740,1776,2614,2620,2702,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1450 1596 4
  · have he : independentCachedBranchMembers1450.erase 1596=independentCachedBranchMembers1448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1448
  · have he : independentCachedBranchMembers1450.filter (independentCachedEdge 1596)=independentCachedBranchMembers1449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1449
def independentCachedBranchMembers1451 : Finset ℕ := ([12,1652,1714,1734,1776,2620,2702,2764,3186,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1451 4 (fun x => (if x<2620 then (if x<1714 then (if x<1652 then 0 else 1) else (if x<1734 then 0 else (if x<1776 then 1 else 2))) else (if x<2764 then (if x<2702 then 1 else 1) else (if x<3186 then 0 else (if x<3252 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1452 : Finset ℕ := ([12,48,192,1596,1652,1714,1734,1740,1776,2614,2620,2702,2758,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1452 2758 4
  · have he : independentCachedBranchMembers1452.erase 2758=independentCachedBranchMembers1450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1450
  · have he : independentCachedBranchMembers1452.filter (independentCachedEdge 2758)=independentCachedBranchMembers1451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1451
def independentCachedBranchMembers1453 : Finset ℕ := ([192,1596,1652,1714,1734,2614,2764,2800,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1453 4 (fun x => (if x<2614 then (if x<1652 then (if x<1596 then 0 else 0) else (if x<1714 then 1 else (if x<1734 then 1 else 1))) else (if x<2800 then (if x<2764 then 0 else 2) else (if x<3192 then 2 else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1454 : Finset ℕ := ([12,48,192,1596,1652,1714,1734,1740,1776,2614,2620,2702,2738,2758,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1454 2738 4
  · have he : independentCachedBranchMembers1454.erase 2738=independentCachedBranchMembers1452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1452
  · have he : independentCachedBranchMembers1454.filter (independentCachedEdge 2738)=independentCachedBranchMembers1453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1453
def independentCachedBranchMembers1455 : Finset ℕ := ([12,192,1596,1714,1734,1776,2614,2702,2764,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1455 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1455 4 (fun x => (if x<1776 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 1 else 1))) else (if x<2764 then (if x<2614 then 0 else (if x<2702 then 2 else 2)) else (if x<3186 then 1 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1456 : Finset ℕ := ([12,48,192,1596,1652,1714,1720,1734,1740,1776,2614,2620,2702,2738,2758,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1456 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1456 1720 4
  · have he : independentCachedBranchMembers1456.erase 1720=independentCachedBranchMembers1454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1454
  · have he : independentCachedBranchMembers1456.filter (independentCachedEdge 1720)=independentCachedBranchMembers1455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1455
def independentCachedBranchMembers1457 : Finset ℕ := ([192,1652,1734,1740,1776,2614,2620,2702,2738,3130,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1457 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1457 4 (fun x => (if x<2614 then (if x<1734 then (if x<1652 then 0 else 1) else (if x<1740 then 0 else (if x<1776 then 1 else 0))) else (if x<2738 then (if x<2620 then 1 else (if x<2702 then 2 else 1)) else (if x<3130 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1458 : Finset ℕ := ([12,48,192,1596,1652,1678,1714,1720,1734,1740,1776,2614,2620,2702,2738,2758,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1458 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1458 1678 4
  · have he : independentCachedBranchMembers1458.erase 1678=independentCachedBranchMembers1456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1456
  · have he : independentCachedBranchMembers1458.filter (independentCachedEdge 1678)=independentCachedBranchMembers1457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1457
def independentCachedBranchMembers1459 : Finset ℕ := ([12,1596,1652,1714,1740,2614,2702,2758,2800,3150,3192] : List ℕ).toFinset
theorem independentCachedBranchBound1459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1459 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1459 4 (fun x => (if x<2614 then (if x<1652 then (if x<1596 then 0 else 0) else (if x<1714 then 1 else (if x<1740 then 0 else 1))) else (if x<2800 then (if x<2702 then 1 else (if x<2758 then 1 else 2)) else (if x<3150 then 2 else (if x<3192 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1460 : Finset ℕ := ([12,48,192,1590,1596,1652,1678,1714,1720,1734,1740,1776,2614,2620,2702,2738,2758,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1460 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1460 1590 4
  · have he : independentCachedBranchMembers1460.erase 1590=independentCachedBranchMembers1458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1458
  · have he : independentCachedBranchMembers1460.filter (independentCachedEdge 1590)=independentCachedBranchMembers1459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1459
def independentCachedBranchMembers1461 : Finset ℕ := ([1590,1678,1714,1734,2614,2702,2738,2758,3130,3150,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1461 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1461 4 (fun x => (if x<2738 then (if x<1734 then (if x<1678 then 0 else (if x<1714 then 0 else 1)) else (if x<2614 then 1 else (if x<2702 then 2 else 2))) else (if x<3150 then (if x<2758 then 3 else (if x<3130 then 3 else 1)) else (if x<3186 then 1 else (if x<3274 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1462 : Finset ℕ := ([12,48,192,252,1590,1596,1652,1678,1714,1720,1734,1740,1776,2614,2620,2702,2738,2758,2764,2800,3130,3150,3186,3192,3252,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1462 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1462 252 4
  · have he : independentCachedBranchMembers1462.erase 252=independentCachedBranchMembers1460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1460
  · have he : independentCachedBranchMembers1462.filter (independentCachedEdge 252)=independentCachedBranchMembers1461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1461
def independentCachedBranchMembers1463 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2662,2668,2702,2716,2730,2738,2758,2764,2772,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1463 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1463 3178 5
  · have he : independentCachedBranchMembers1463.erase 3178=independentCachedBranchMembers1441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1441
  · have he : independentCachedBranchMembers1463.filter (independentCachedEdge 3178)=independentCachedBranchMembers1462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1462
def independentCachedBranchMembers1464 : Finset ℕ := ([48,252,1590,1626,1644,1678,1720,1748,2620,2662,2716,2730,2738,2758,2792,2800,3130,3150,3158,3192,3226,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1464 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1464 5 (fun x => (if x<2738 then (if x<1720 then (if x<1626 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 1 else (if x<1678 then 1 else 1))) else (if x<2662 then (if x<1748 then 0 else (if x<2620 then 1 else 0)) else (if x<2716 then 2 else (if x<2730 then 3 else 2)))) else (if x<3158 then (if x<2800 then (if x<2758 then 3 else (if x<2792 then 3 else 3)) else (if x<3130 then 0 else (if x<3150 then 4 else 4))) else (if x<3244 then (if x<3192 then 2 else (if x<3226 then 0 else 2)) else (if x<3252 then 4 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1465 : Finset ℕ := ([1590,1644,1678,1748,2620,2662,2730,2800,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1465 4 (fun x => (if x<2730 then (if x<1748 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<2800 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1466 : Finset ℕ := ([48,252,1590,1626,1644,1678,1720,1740,1748,2620,2662,2716,2730,2738,2758,2792,2800,3130,3150,3158,3192,3226,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1466 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1466 1740 4
  · have he : independentCachedBranchMembers1466.erase 1740=independentCachedBranchMembers1464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1464
  · have he : independentCachedBranchMembers1466.filter (independentCachedEdge 1740)=independentCachedBranchMembers1465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1465
def independentCachedBranchMembers1467 : Finset ℕ := ([1590,1644,1678,1748,2716,2738,2758,2792,3130,3150,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1467 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1467 4 (fun x => (if x<2758 then (if x<1748 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<2716 then 0 else (if x<2738 then 1 else 1))) else (if x<3150 then (if x<2792 then 1 else (if x<3130 then 1 else 2)) else (if x<3244 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1468 : Finset ℕ := ([48,252,1590,1626,1644,1652,1678,1720,1740,1748,2620,2662,2716,2730,2738,2758,2792,2800,3130,3150,3158,3192,3226,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1468 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1468 1652 4
  · have he : independentCachedBranchMembers1468.erase 1652=independentCachedBranchMembers1466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1466
  · have he : independentCachedBranchMembers1468.filter (independentCachedEdge 1652)=independentCachedBranchMembers1467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1467
def independentCachedBranchMembers1469 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2662,2668,2702,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1469 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1469 2786 5
  · have he : independentCachedBranchMembers1469.erase 2786=independentCachedBranchMembers1463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1463
  · have he : independentCachedBranchMembers1469.filter (independentCachedEdge 2786)=independentCachedBranchMembers1468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1468
def independentCachedBranchMembers1470 : Finset ℕ := ([12,48,192,252,1596,1720,1740,1776,2614,2668,2702,2716,2738,2758,2772,2792,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1470 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1470 5 (fun x => (if x<2738 then (if x<1740 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1596 then 0 else (if x<1720 then 0 else 1))) else (if x<2668 then (if x<1776 then 0 else (if x<2614 then 0 else 2)) else (if x<2702 then 2 else (if x<2716 then 2 else 1)))) else (if x<3164 then (if x<2792 then (if x<2758 then 1 else (if x<2772 then 1 else 2)) else (if x<3130 then 1 else (if x<3150 then 3 else 3))) else (if x<3274 then (if x<3186 then 4 else (if x<3244 then 4 else 3)) else (if x<3288 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1471 : Finset ℕ := ([12,192,1596,1776,2716,2738,2758,2792,3130,3150,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1471 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1471 4 (fun x => (if x<2758 then (if x<1776 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<2716 then 0 else (if x<2738 then 1 else 1))) else (if x<3150 then (if x<2792 then 1 else (if x<3130 then 1 else 2)) else (if x<3244 then 2 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1472 : Finset ℕ := ([12,48,192,252,1596,1652,1720,1740,1776,2614,2668,2702,2716,2738,2758,2772,2792,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1472 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1472 1652 4
  · have he : independentCachedBranchMembers1472.erase 1652=independentCachedBranchMembers1470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1470
  · have he : independentCachedBranchMembers1472.filter (independentCachedEdge 1652)=independentCachedBranchMembers1471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1471
def independentCachedBranchMembers1473 : Finset ℕ := ([12,48,192,252,2614,2668,2702,2716,2738,2758,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound1473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1473 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1473 4 (fun x => (if x<2702 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<2614 then 0 else (if x<2668 then 1 else 1))) else (if x<2758 then (if x<2716 then 1 else (if x<2738 then 2 else 2)) else (if x<2772 then 2 else (if x<2792 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1474 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1720,1740,1776,2614,2668,2702,2716,2738,2758,2772,2792,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1474 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1474 1626 4
  · have he : independentCachedBranchMembers1474.erase 1626=independentCachedBranchMembers1472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1472
  · have he : independentCachedBranchMembers1474.filter (independentCachedEdge 1626)=independentCachedBranchMembers1473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1473
def independentCachedBranchMembers1475 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2614,2620,2650,2662,2668,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1475 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1475 2710 5
  · have he : independentCachedBranchMembers1475.erase 2710=independentCachedBranchMembers1469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1469
  · have he : independentCachedBranchMembers1475.filter (independentCachedEdge 2710)=independentCachedBranchMembers1474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1474
def independentCachedBranchMembers1476 : Finset ℕ := ([48,252,1626,1652,1692,1714,1734,1768,2614,2620,2662,2668,2702,2730,2772,2800,3158,3164,3186,3192,3226,3252,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1476 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1476 5 (fun x => (if x<2702 then (if x<1734 then (if x<1652 then (if x<252 then 0 else (if x<1626 then 0 else 1)) else (if x<1692 then 0 else (if x<1714 then 1 else 1))) else (if x<2620 then (if x<1768 then 1 else (if x<2614 then 1 else 2)) else (if x<2662 then 0 else (if x<2668 then 3 else 2)))) else (if x<3186 then (if x<2800 then (if x<2730 then 2 else (if x<2772 then 3 else 2)) else (if x<3158 then 0 else (if x<3164 then 3 else 4))) else (if x<3252 then (if x<3192 then 4 else (if x<3226 then 0 else 3)) else (if x<3274 then 0 else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1477 : Finset ℕ := ([1692,1714,1734,1768,2620,2662,2730,2800,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1477 4 (fun x => (if x<2730 then (if x<1768 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<2800 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1478 : Finset ℕ := ([48,252,1626,1652,1692,1714,1734,1740,1768,2614,2620,2662,2668,2702,2730,2772,2800,3158,3164,3186,3192,3226,3252,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1478 1740 4
  · have he : independentCachedBranchMembers1478.erase 1740=independentCachedBranchMembers1476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1476
  · have he : independentCachedBranchMembers1478.filter (independentCachedEdge 1740)=independentCachedBranchMembers1477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1477
def independentCachedBranchMembers1479 : Finset ℕ := ([1692,1714,1734,1768,2614,2668,2702,2772,3164,3186,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1479 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1479 4 (fun x => (if x<2702 then (if x<1768 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2614 then 0 else (if x<2668 then 1 else 1))) else (if x<3186 then (if x<2772 then 1 else (if x<3164 then 1 else 2)) else (if x<3274 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1480 : Finset ℕ := ([48,252,1626,1652,1692,1714,1720,1734,1740,1768,2614,2620,2662,2668,2702,2730,2772,2800,3158,3164,3186,3192,3226,3252,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1480 1720 4
  · have he : independentCachedBranchMembers1480.erase 1720=independentCachedBranchMembers1478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1478
  · have he : independentCachedBranchMembers1480.filter (independentCachedEdge 1720)=independentCachedBranchMembers1479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1479
def independentCachedBranchMembers1481 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1692,1714,1720,1734,1740,1748,1768,1776,2606,2614,2620,2650,2662,2668,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1481 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1481 2606 5
  · have he : independentCachedBranchMembers1481.erase 2606=independentCachedBranchMembers1475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1475
  · have he : independentCachedBranchMembers1481.filter (independentCachedEdge 2606)=independentCachedBranchMembers1480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1480
def independentCachedBranchMembers1482 : Finset ℕ := ([1590,1644,1678,1692,1714,1734,1748,1768,2606,2620,2650,2662,2710,2730,2764,2786,2800,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1482 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1482 5 (fun x => (if x<2710 then (if x<1748 then (if x<1692 then (if x<1644 then 0 else (if x<1678 then 0 else 0)) else (if x<1714 then 1 else (if x<1734 then 1 else 1))) else (if x<2620 then (if x<1768 then 0 else (if x<2606 then 1 else 0)) else (if x<2650 then 2 else (if x<2662 then 2 else 2)))) else (if x<3150 then (if x<2786 then (if x<2730 then 0 else (if x<2764 then 2 else 0)) else (if x<2800 then 1 else (if x<3130 then 2 else 3))) else (if x<3244 then (if x<3164 then 3 else (if x<3186 then 4 else 4)) else (if x<3288 then (if x<3274 then 3 else 4) else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1483 : Finset ℕ := ([1644,1678,1692,1714,2650,2662,2710,2730,3150,3164,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound1483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1483 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1483 4 (fun x => (if x<2710 then (if x<1714 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 2 else 2))) else (if x<3164 then (if x<2730 then 0 else (if x<3150 then 2 else 3)) else (if x<3186 then 1 else (if x<3244 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1484 : Finset ℕ := ([192,1590,1644,1678,1692,1714,1734,1748,1768,2606,2620,2650,2662,2710,2730,2764,2786,2800,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1484 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1484 192 4
  · have he : independentCachedBranchMembers1484.erase 192=independentCachedBranchMembers1482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1482
  · have he : independentCachedBranchMembers1484.filter (independentCachedEdge 192)=independentCachedBranchMembers1483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1483
def independentCachedBranchMembers1485 : Finset ℕ := ([1590,1734,1748,1768,2650,2662,2710,2730,3130,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1485 4 (fun x => (if x<2710 then (if x<1768 then (if x<1734 then 0 else (if x<1748 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 2 else 0))) else (if x<3274 then (if x<2730 then 0 else (if x<3130 then 1 else 2)) else (if x<3288 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1486 : Finset ℕ := ([12,192,1590,1644,1678,1692,1714,1734,1748,1768,2606,2620,2650,2662,2710,2730,2764,2786,2800,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1486 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1486 12 4
  · have he : independentCachedBranchMembers1486.erase 12=independentCachedBranchMembers1484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1484
  · have he : independentCachedBranchMembers1486.filter (independentCachedEdge 12)=independentCachedBranchMembers1485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1485
def independentCachedBranchMembers1487 : Finset ℕ := ([1590,1678,1714,1734,2650,2662,2710,2730,3130,3150,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1487 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1487 4 (fun x => (if x<2710 then (if x<1734 then (if x<1678 then 0 else (if x<1714 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 2 else 2))) else (if x<3150 then (if x<2730 then 0 else (if x<3130 then 2 else 1)) else (if x<3186 then 1 else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1488 : Finset ℕ := ([1590,1678,2662,2730,3130,3150] : List ℕ).toFinset
theorem independentCachedBranchBound1488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1488 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1488 3 (fun x => (if x<2730 then (if x<1678 then 0 else (if x<2662 then 0 else 1)) else (if x<3130 then 1 else (if x<3150 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1489 : Finset ℕ := ([1590,1678,1714,1734,2650,2662,2710,2730,2786,3130,3150,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1489 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1489 2786 3
  · have he : independentCachedBranchMembers1489.erase 2786=independentCachedBranchMembers1487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1487
  · have he : independentCachedBranchMembers1489.filter (independentCachedEdge 2786)=independentCachedBranchMembers1488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1488
def independentCachedBranchMembers1490 : Finset ℕ := ([1714,1734,2662,2730,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1490 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1490 3 (fun x => (if x<2730 then (if x<1734 then 0 else (if x<2662 then 0 else 1)) else (if x<3186 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1491 : Finset ℕ := ([1590,1678,1714,1734,2606,2650,2662,2710,2730,2786,3130,3150,3186,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1491 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1491 2606 3
  · have he : independentCachedBranchMembers1491.erase 2606=independentCachedBranchMembers1489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1489
  · have he : independentCachedBranchMembers1491.filter (independentCachedEdge 2606)=independentCachedBranchMembers1490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1490
def independentCachedBranchMembers1492 : Finset ℕ := ([12,192,252,1590,1644,1678,1692,1714,1734,1748,1768,2606,2620,2650,2662,2710,2730,2764,2786,2800,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1492 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1492 252 4
  · have he : independentCachedBranchMembers1492.erase 252=independentCachedBranchMembers1486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1486
  · have he : independentCachedBranchMembers1492.filter (independentCachedEdge 252)=independentCachedBranchMembers1491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1491
def independentCachedBranchMembers1493 : Finset ℕ := ([1644,1692,1748,1768,2650,2662,2710,2730,2786,3164,3244,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1493 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1493 4 (fun x => (if x<2710 then (if x<1768 then (if x<1692 then 0 else (if x<1748 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 2 else 0))) else (if x<3164 then (if x<2730 then 0 else (if x<2786 then 1 else 2)) else (if x<3288 then (if x<3244 then 2 else 3) else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1494 : Finset ℕ := ([1692,1768,2662,2730,3164,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1494 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1494 3 (fun x => (if x<2730 then (if x<1768 then 0 else (if x<2662 then 0 else 1)) else (if x<3164 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1495 : Finset ℕ := ([1644,1692,1748,1768,2606,2650,2662,2710,2730,2786,3164,3244,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1495 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1495 2606 3
  · have he : independentCachedBranchMembers1495.erase 2606=independentCachedBranchMembers1493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1493
  · have he : independentCachedBranchMembers1495.filter (independentCachedEdge 2606)=independentCachedBranchMembers1494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1494
def independentCachedBranchMembers1496 : Finset ℕ := ([12,48,192,252,1590,1644,1678,1692,1714,1734,1748,1768,2606,2620,2650,2662,2710,2730,2764,2786,2800,3130,3150,3164,3186,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1496 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1496 48 4
  · have he : independentCachedBranchMembers1496.erase 48=independentCachedBranchMembers1492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1492
  · have he : independentCachedBranchMembers1496.filter (independentCachedEdge 48)=independentCachedBranchMembers1495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1495
def independentCachedBranchMembers1497 : Finset ℕ := ([12,48,192,252,1590,1596,1626,1644,1652,1678,1686,1692,1714,1720,1734,1740,1748,1768,1776,2606,2614,2620,2650,2662,2668,2702,2710,2716,2730,2738,2758,2764,2772,2786,2792,2800,3102,3130,3150,3158,3164,3178,3186,3192,3226,3238,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1497 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1497 1686 5
  · have he : independentCachedBranchMembers1497.erase 1686=independentCachedBranchMembers1481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1481
  · have he : independentCachedBranchMembers1497.filter (independentCachedEdge 1686)=independentCachedBranchMembers1496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1496
def independentCachedBranchMembers1498 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1498 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1498 3162 6
  · have he : independentCachedBranchMembers1498.erase 3162=independentCachedBranchMembers1366 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1366
  · have he : independentCachedBranchMembers1498.filter (independentCachedEdge 3162)=independentCachedBranchMembers1497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1497
def independentCachedBranchMembers1499 : Finset ℕ := ([1596,1614,1650,1702,1748,1768,2620,2650,2662,2710,2730,2764,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1499 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1499 6 (fun x => (if x<3118 then (if x<2650 then (if x<1702 then (if x<1614 then 0 else (if x<1650 then 0 else 0)) else (if x<1768 then (if x<1748 then 0 else 0) else (if x<2620 then 0 else 1))) else (if x<2730 then (if x<2662 then 1 else (if x<2710 then 1 else 1)) else (if x<2800 then (if x<2764 then 1 else 1) else (if x<3102 then 1 else 2)))) else (if x<3228 then (if x<3164 then (if x<3126 then 3 else (if x<3130 then 4 else 5)) else (if x<3188 then (if x<3180 then 3 else 2) else (if x<3192 then 5 else 4))) else (if x<3270 then (if x<3252 then (if x<3244 then 4 else 5) else (if x<3256 then 2 else 3)) else (if x<3282 then (if x<3274 then 2 else 3) else (if x<3298 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1500 : Finset ℕ := ([1596,1702,2650,2662,2710,2730,3118,3130,3180,3192,3228,3252,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1500 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1500 5 (fun x => (if x<3130 then (if x<2662 then (if x<1702 then 0 else (if x<2650 then 0 else 1)) else (if x<2730 then (if x<2710 then 1 else 1) else (if x<3118 then 1 else 0))) else (if x<3228 then (if x<3180 then 2 else (if x<3192 then 2 else 0)) else (if x<3274 then (if x<3252 then 2 else 0) else (if x<3298 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1501 : Finset ℕ := ([1596,1614,1650,1702,1748,1768,2620,2646,2650,2662,2710,2730,2764,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1501 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1501 2646 5
  · have he : independentCachedBranchMembers1501.erase 2646=independentCachedBranchMembers1499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1499
  · have he : independentCachedBranchMembers1501.filter (independentCachedEdge 2646)=independentCachedBranchMembers1500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1500
def independentCachedBranchMembers1502 : Finset ℕ := ([1596,1614,1650,2650,2662,2764,2800,3118,3126,3164,3192,3228,3256,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1502 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1502 5 (fun x => (if x<3118 then (if x<2650 then (if x<1614 then 0 else (if x<1650 then 0 else 0)) else (if x<2764 then (if x<2662 then 1 else 1) else (if x<2800 then 1 else 1))) else (if x<3228 then (if x<3164 then (if x<3126 then 2 else 3) else (if x<3192 then 2 else 3)) else (if x<3274 then (if x<3256 then 3 else 2) else (if x<3282 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1503 : Finset ℕ := ([1596,1614,1650,1702,1748,1768,2620,2646,2650,2662,2710,2730,2764,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1503 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1503 2788 5
  · have he : independentCachedBranchMembers1503.erase 2788=independentCachedBranchMembers1501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1501
  · have he : independentCachedBranchMembers1503.filter (independentCachedEdge 2788)=independentCachedBranchMembers1502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1502
def independentCachedBranchMembers1504 : Finset ℕ := ([1596,1614,1650,2650,2662,2764,2800,3102,3130,3180,3188,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1504 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1504 5 (fun x => (if x<3102 then (if x<2650 then (if x<1614 then 0 else (if x<1650 then 0 else 0)) else (if x<2764 then (if x<2662 then 1 else 1) else (if x<2800 then 1 else 1))) else (if x<3244 then (if x<3180 then (if x<3130 then 2 else 3) else (if x<3188 then 2 else 3)) else (if x<3270 then (if x<3252 then 3 else 2) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1505 : Finset ℕ := ([1596,1614,1650,1702,1748,1768,2620,2646,2650,2662,2710,2730,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1505 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1505 2776 5
  · have he : independentCachedBranchMembers1505.erase 2776=independentCachedBranchMembers1503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1503
  · have he : independentCachedBranchMembers1505.filter (independentCachedEdge 2776)=independentCachedBranchMembers1504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1504
def independentCachedBranchMembers1506 : Finset ℕ := ([1596,1748,1768,2710,2730,2764,2800,3102,3118,3188,3192,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1506 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1506 5 (fun x => (if x<3102 then (if x<2710 then (if x<1748 then 0 else (if x<1768 then 0 else 0)) else (if x<2764 then (if x<2730 then 1 else 1) else (if x<2800 then 1 else 1))) else (if x<3228 then (if x<3188 then (if x<3118 then 2 else 3) else (if x<3192 then 2 else 3)) else (if x<3270 then (if x<3244 then 3 else 2) else (if x<3274 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1507 : Finset ℕ := ([1596,1614,1650,1702,1748,1768,2620,2646,2650,2662,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1507 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1507 2738 5
  · have he : independentCachedBranchMembers1507.erase 2738=independentCachedBranchMembers1505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1505
  · have he : independentCachedBranchMembers1507.filter (independentCachedEdge 2738)=independentCachedBranchMembers1506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1506
def independentCachedBranchMembers1508 : Finset ℕ := ([1596,1748,1768,2710,2730,2764,2800,3126,3130,3164,3180,3252,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1508 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1508 5 (fun x => (if x<3126 then (if x<2710 then (if x<1748 then 0 else (if x<1768 then 0 else 0)) else (if x<2764 then (if x<2730 then 1 else 1) else (if x<2800 then 1 else 1))) else (if x<3252 then (if x<3164 then (if x<3130 then 2 else 3) else (if x<3180 then 2 else 3)) else (if x<3282 then (if x<3256 then 3 else 2) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1509 : Finset ℕ := ([1596,1614,1650,1702,1748,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1509 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1509 2702 5
  · have he : independentCachedBranchMembers1509.erase 2702=independentCachedBranchMembers1507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1507
  · have he : independentCachedBranchMembers1509.filter (independentCachedEdge 2702)=independentCachedBranchMembers1508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1508
def independentCachedBranchMembers1510 : Finset ℕ := ([1702,1748,1768,2620,2646,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3228,3256,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1510 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1510 5 (fun x => (if x<2776 then (if x<2646 then (if x<1768 then (if x<1748 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2710 then (if x<2702 then 1 else 1) else (if x<2730 then 0 else (if x<2738 then 0 else 1)))) else (if x<3192 then (if x<3118 then (if x<2788 then 0 else 0) else (if x<3126 then 2 else (if x<3164 then 3 else 2))) else (if x<3256 then (if x<3228 then 3 else 3) else (if x<3274 then 2 else (if x<3282 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1511 : Finset ℕ := ([1596,1614,1650,1702,1748,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1511 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1511 1764 5
  · have he : independentCachedBranchMembers1511.erase 1764=independentCachedBranchMembers1509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1509
  · have he : independentCachedBranchMembers1511.filter (independentCachedEdge 1764)=independentCachedBranchMembers1510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1510
def independentCachedBranchMembers1512 : Finset ℕ := ([1702,1748,1768,2620,2646,2702,2710,2730,2738,2776,2788,3102,3130,3180,3188,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1512 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1512 5 (fun x => (if x<2776 then (if x<2646 then (if x<1768 then (if x<1748 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2710 then (if x<2702 then 1 else 1) else (if x<2730 then 0 else (if x<2738 then 0 else 1)))) else (if x<3188 then (if x<3102 then (if x<2788 then 0 else 0) else (if x<3130 then 2 else (if x<3180 then 3 else 2))) else (if x<3252 then (if x<3244 then 3 else 3) else (if x<3270 then 2 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1513 : Finset ℕ := ([1596,1614,1650,1702,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1513 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1513 1752 5
  · have he : independentCachedBranchMembers1513.erase 1752=independentCachedBranchMembers1511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1511
  · have he : independentCachedBranchMembers1513.filter (independentCachedEdge 1752)=independentCachedBranchMembers1512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1512
def independentCachedBranchMembers1514 : Finset ℕ := ([1614,1650,1702,2620,2646,2650,2662,2702,2738,2776,2788,3102,3118,3188,3192,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1514 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1514 5 (fun x => (if x<2776 then (if x<2646 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2662 then (if x<2650 then 1 else 0) else (if x<2702 then 0 else (if x<2738 then 0 else 0)))) else (if x<3192 then (if x<3102 then (if x<2788 then 1 else 1) else (if x<3118 then 2 else (if x<3188 then 3 else 2))) else (if x<3244 then (if x<3228 then 3 else 3) else (if x<3270 then 2 else (if x<3274 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1515 : Finset ℕ := ([1596,1614,1650,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1515 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1515 1714 5
  · have he : independentCachedBranchMembers1515.erase 1714=independentCachedBranchMembers1513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1513
  · have he : independentCachedBranchMembers1515.filter (independentCachedEdge 1714)=independentCachedBranchMembers1514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1514
def independentCachedBranchMembers1516 : Finset ℕ := ([1614,1650,1702,2620,2646,2650,2662,2702,2738,2776,2788,3126,3130,3164,3180,3252,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1516 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1516 5 (fun x => (if x<2776 then (if x<2646 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2662 then (if x<2650 then 1 else 0) else (if x<2702 then 0 else (if x<2738 then 0 else 0)))) else (if x<3180 then (if x<3126 then (if x<2788 then 1 else 1) else (if x<3130 then 2 else (if x<3164 then 3 else 2))) else (if x<3256 then (if x<3252 then 3 else 3) else (if x<3282 then 2 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1517 : Finset ℕ := ([1596,1614,1650,1678,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1517 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1517 1678 5
  · have he : independentCachedBranchMembers1517.erase 1678=independentCachedBranchMembers1515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1515
  · have he : independentCachedBranchMembers1517.filter (independentCachedEdge 1678)=independentCachedBranchMembers1516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1516
def independentCachedBranchMembers1518 : Finset ℕ := ([1678,1702,1714,1748,1768,2620,2650,2662,2710,2730,2764,2776,2788,2800,3118,3130,3164,3188,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1518 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1518 5 (fun x => (if x<2776 then (if x<2620 then (if x<1714 then (if x<1702 then 0 else 1) else (if x<1748 then 0 else (if x<1768 then 0 else 0))) else (if x<2710 then (if x<2650 then 2 else (if x<2662 then 1 else 1)) else (if x<2730 then 0 else (if x<2764 then 0 else 0)))) else (if x<3164 then (if x<2800 then (if x<2788 then 2 else 2) else (if x<3118 then 0 else (if x<3130 then 3 else 4))) else (if x<3256 then (if x<3188 then 3 else (if x<3244 then 4 else 4)) else (if x<3274 then 3 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1519 : Finset ℕ := ([1596,1614,1650,1678,1686,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1519 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1519 1686 5
  · have he : independentCachedBranchMembers1519.erase 1686=independentCachedBranchMembers1517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1517
  · have he : independentCachedBranchMembers1519.filter (independentCachedEdge 1686)=independentCachedBranchMembers1518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1518
def independentCachedBranchMembers1520 : Finset ℕ := ([1614,1650,1702,1752,1764,2620,2650,2662,2702,2710,2730,2738,2764,2800,3118,3126,3180,3188,3228,3256,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1520 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1520 5 (fun x => (if x<2738 then (if x<2620 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1752 then 0 else (if x<1764 then 1 else 1))) else (if x<2702 then (if x<2650 then 2 else (if x<2662 then 0 else 0)) else (if x<2710 then 0 else (if x<2730 then 2 else 2)))) else (if x<3180 then (if x<2800 then (if x<2764 then 0 else 1) else (if x<3118 then 1 else (if x<3126 then 3 else 4))) else (if x<3256 then (if x<3188 then 4 else (if x<3228 then 3 else 3)) else (if x<3270 then 4 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1521 : Finset ℕ := ([1596,1614,1626,1650,1678,1686,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1521 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1521 1626 5
  · have he : independentCachedBranchMembers1521.erase 1626=independentCachedBranchMembers1519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1519
  · have he : independentCachedBranchMembers1521.filter (independentCachedEdge 1626)=independentCachedBranchMembers1520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1520
def independentCachedBranchMembers1522 : Finset ℕ := ([1596,1650,1702,1714,1764,1768,2620,2662,2730,2738,2788,2800,3118,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1522 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1522 5 (fun x => (if x<2800 then (if x<1768 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<1714 then 0 else (if x<1764 then 1 else 1))) else (if x<2730 then (if x<2620 then 0 else (if x<2662 then 2 else 2)) else (if x<2738 then 2 else (if x<2788 then 3 else 3)))) else (if x<3188 then (if x<3126 then (if x<3118 then 1 else 2) else (if x<3130 then 0 else (if x<3180 then 3 else 3))) else (if x<3252 then (if x<3192 then 2 else (if x<3244 then 0 else 0)) else (if x<3256 then 1 else (if x<3298 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1523 : Finset ℕ := ([222,1596,1614,1626,1650,1678,1686,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1523 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1523 222 5
  · have he : independentCachedBranchMembers1523.erase 222=independentCachedBranchMembers1521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1521
  · have he : independentCachedBranchMembers1523.filter (independentCachedEdge 222)=independentCachedBranchMembers1522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1522
def independentCachedBranchMembers1524 : Finset ℕ := ([1596,1614,1714,1752,1768,2620,2646,2662,2730,2738,2776,2800,3102,3118,3126,3164,3180,3188,3256,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1524 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1524 5 (fun x => (if x<2800 then (if x<2620 then (if x<1714 then (if x<1614 then 0 else 0) else (if x<1752 then 1 else (if x<1768 then 0 else 1))) else (if x<2730 then (if x<2646 then 2 else (if x<2662 then 2 else 3)) else (if x<2738 then 1 else (if x<2776 then 2 else 2)))) else (if x<3180 then (if x<3118 then (if x<3102 then 1 else 4) else (if x<3126 then 0 else (if x<3164 then 2 else 0))) else (if x<3274 then (if x<3188 then 3 else (if x<3256 then 4 else 0)) else (if x<3282 then 0 else (if x<3298 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1525 : Finset ℕ := ([132,222,1596,1614,1626,1650,1678,1686,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1525 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1525 132 5
  · have he : independentCachedBranchMembers1525.erase 132=independentCachedBranchMembers1523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1523
  · have he : independentCachedBranchMembers1525.filter (independentCachedEdge 132)=independentCachedBranchMembers1524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1524
def independentCachedBranchMembers1526 : Finset ℕ := ([1596,1650,1678,1748,1764,2620,2646,2662,2702,2730,2788,2800,3102,3118,3130,3188,3228,3244,3256,3270,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1526 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1526 5 (fun x => (if x<2800 then (if x<2620 then (if x<1678 then (if x<1650 then 0 else 0) else (if x<1748 then 1 else (if x<1764 then 0 else 1))) else (if x<2702 then (if x<2646 then 2 else (if x<2662 then 2 else 3)) else (if x<2730 then 2 else (if x<2788 then 3 else 2)))) else (if x<3228 then (if x<3118 then (if x<3102 then 1 else 1) else (if x<3130 then 3 else (if x<3188 then 0 else 0))) else (if x<3270 then (if x<3244 then 0 else (if x<3256 then 2 else 3)) else (if x<3282 then 2 else (if x<3298 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1527 : Finset ℕ := ([72,132,222,1596,1614,1626,1650,1678,1686,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1527 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1527 72 5
  · have he : independentCachedBranchMembers1527.erase 72=independentCachedBranchMembers1525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1525
  · have he : independentCachedBranchMembers1527.filter (independentCachedEdge 72)=independentCachedBranchMembers1526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1526
def independentCachedBranchMembers1528 : Finset ℕ := ([1596,1614,1678,1702,1748,1752,2620,2662,2702,2730,2776,2800,3118,3164,3188,3192,3228,3252,3256,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1528 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1528 5 (fun x => (if x<2800 then (if x<1752 then (if x<1678 then (if x<1614 then 0 else 0) else (if x<1702 then 1 else (if x<1748 then 0 else 0))) else (if x<2702 then (if x<2620 then 1 else (if x<2662 then 2 else 2)) else (if x<2730 then 2 else (if x<2776 then 3 else 3)))) else (if x<3228 then (if x<3164 then (if x<3118 then 1 else 0) else (if x<3188 then 0 else (if x<3192 then 2 else 1))) else (if x<3270 then (if x<3252 then 2 else (if x<3256 then 0 else 3)) else (if x<3274 then 0 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1529 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1650,1678,1686,1702,1714,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1529 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1529 18 5
  · have he : independentCachedBranchMembers1529.erase 18=independentCachedBranchMembers1527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1527
  · have he : independentCachedBranchMembers1529.filter (independentCachedEdge 18)=independentCachedBranchMembers1528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1528
def independentCachedBranchMembers1530 : Finset ℕ := ([1614,1650,1678,1714,1748,1752,1764,1768,2620,2646,2650,2662,2710,2730,2764,2800,3102,3118,3188,3192,3252,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1530 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1530 5 (fun x => (if x<2710 then (if x<1764 then (if x<1714 then (if x<1650 then 0 else (if x<1678 then 0 else 1)) else (if x<1748 then 1 else (if x<1752 then 0 else 1))) else (if x<2646 then (if x<1768 then 1 else (if x<2620 then 0 else 2)) else (if x<2650 then 0 else (if x<2662 then 2 else 2)))) else (if x<3188 then (if x<2800 then (if x<2730 then 2 else (if x<2764 then 2 else 0)) else (if x<3102 then 0 else (if x<3118 then 3 else 4))) else (if x<3256 then (if x<3192 then 3 else (if x<3252 then 4 else 4)) else (if x<3282 then 3 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1531 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1531 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1531 1740 5
  · have he : independentCachedBranchMembers1531.erase 1740=independentCachedBranchMembers1529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1529
  · have he : independentCachedBranchMembers1531.filter (independentCachedEdge 1740)=independentCachedBranchMembers1530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1530
def independentCachedBranchMembers1532 : Finset ℕ := ([18,222,1614,1626,1650,1686,1748,1768,2620,2646,2702,2738,2764,2776,2788,2800,3102,3126,3164,3188,3244,3256,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1532 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1532 5 (fun x => (if x<2764 then (if x<1748 then (if x<1626 then (if x<222 then 0 else (if x<1614 then 0 else 1)) else (if x<1650 then 0 else (if x<1686 then 1 else 0))) else (if x<2646 then (if x<1768 then 1 else (if x<2620 then 1 else 2)) else (if x<2702 then 0 else (if x<2738 then 2 else 2)))) else (if x<3164 then (if x<2800 then (if x<2776 then 1 else (if x<2788 then 2 else 2)) else (if x<3102 then 1 else (if x<3126 then 0 else 3))) else (if x<3256 then (if x<3188 then 3 else (if x<3244 then 4 else 3)) else (if x<3270 then 4 else (if x<3282 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1533 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1642,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1533 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1533 1642 5
  · have he : independentCachedBranchMembers1533.erase 1642=independentCachedBranchMembers1531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1531
  · have he : independentCachedBranchMembers1533.filter (independentCachedEdge 1642)=independentCachedBranchMembers1532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1532
def independentCachedBranchMembers1534 : Finset ℕ := ([1596,1626,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3118,3130,3164,3188,3228,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1534 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1534 5 (fun x => (if x<2776 then (if x<1748 then (if x<1678 then (if x<1626 then 0 else 0) else (if x<1702 then 0 else (if x<1714 then 1 else 0))) else (if x<2710 then (if x<1768 then 0 else (if x<2646 then 0 else 2)) else (if x<2730 then 1 else (if x<2764 then 1 else 2)))) else (if x<3164 then (if x<2800 then (if x<2788 then 1 else 1) else (if x<3118 then 2 else (if x<3130 then 3 else 4))) else (if x<3252 then (if x<3188 then 3 else (if x<3228 then 4 else 4)) else (if x<3270 then 3 else (if x<3282 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1535 : Finset ℕ := ([1626,1678,1714,2710,2730,2776,2788,3118,3164,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1535 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1535 4 (fun x => (if x<2776 then (if x<1714 then (if x<1678 then 0 else 0) else (if x<2710 then 0 else (if x<2730 then 1 else 1))) else (if x<3164 then (if x<2788 then 1 else (if x<3118 then 1 else 2)) else (if x<3252 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
