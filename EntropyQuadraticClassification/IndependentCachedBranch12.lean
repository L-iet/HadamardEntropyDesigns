/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch11
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1536 : Finset ℕ := ([1596,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3118,3130,3164,3188,3228,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1536 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1536 1650 4
  · have he : independentCachedBranchMembers1536.erase 1650=independentCachedBranchMembers1534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1534
  · have he : independentCachedBranchMembers1536.filter (independentCachedEdge 1650)=independentCachedBranchMembers1535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1535
def independentCachedBranchMembers1537 : Finset ℕ := ([1626,1678,1714,2710,2730,2776,2788,3130,3188,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1537 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1537 4 (fun x => (if x<2776 then (if x<1714 then (if x<1678 then 0 else 0) else (if x<2710 then 0 else (if x<2730 then 1 else 1))) else (if x<3188 then (if x<2788 then 1 else (if x<3130 then 1 else 2)) else (if x<3228 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1538 : Finset ℕ := ([1596,1614,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3118,3130,3164,3188,3228,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1538 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1538 1614 4
  · have he : independentCachedBranchMembers1538.erase 1614=independentCachedBranchMembers1536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1536
  · have he : independentCachedBranchMembers1538.filter (independentCachedEdge 1614)=independentCachedBranchMembers1537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1537
def independentCachedBranchMembers1539 : Finset ℕ := ([1596,1650,1702,1714,1768,2730,2788,2800,3118,3130,3188,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1539 4 (fun x => (if x<2788 then (if x<1714 then (if x<1650 then 0 else (if x<1702 then 0 else 0)) else (if x<1768 then 1 else (if x<2730 then 0 else 1))) else (if x<3130 then (if x<2800 then 2 else (if x<3118 then 1 else 3)) else (if x<3188 then 2 else (if x<3252 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1540 : Finset ℕ := ([222,1596,1614,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3118,3130,3164,3188,3228,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1540 222 4
  · have he : independentCachedBranchMembers1540.erase 222=independentCachedBranchMembers1538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1538
  · have he : independentCachedBranchMembers1540.filter (independentCachedEdge 222)=independentCachedBranchMembers1539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1539
def independentCachedBranchMembers1541 : Finset ℕ := ([1596,1614,1714,1768,2646,2730,2776,2800,3118,3164,3188,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1541 4 (fun x => (if x<2776 then (if x<1768 then (if x<1614 then 0 else (if x<1714 then 0 else 1)) else (if x<2646 then 0 else (if x<2730 then 2 else 1))) else (if x<3164 then (if x<2800 then 2 else (if x<3118 then 1 else 3)) else (if x<3188 then 2 else (if x<3282 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1542 : Finset ℕ := ([132,222,1596,1614,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3118,3130,3164,3188,3228,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1542 132 4
  · have he : independentCachedBranchMembers1542.erase 132=independentCachedBranchMembers1540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1540
  · have he : independentCachedBranchMembers1542.filter (independentCachedEdge 132)=independentCachedBranchMembers1541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1541
def independentCachedBranchMembers1543 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1642,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1543 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1543 2792 5
  · have he : independentCachedBranchMembers1543.erase 2792=independentCachedBranchMembers1533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1533
  · have he : independentCachedBranchMembers1543.filter (independentCachedEdge 2792)=independentCachedBranchMembers1542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1542
def independentCachedBranchMembers1544 : Finset ℕ := ([1596,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3102,3126,3180,3192,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1544 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1544 5 (fun x => (if x<2764 then (if x<1714 then (if x<1650 then (if x<1626 then 0 else 0) else (if x<1678 then 1 else (if x<1702 then 0 else 1))) else (if x<2646 then (if x<1748 then 0 else (if x<1768 then 0 else 0)) else (if x<2710 then 2 else (if x<2730 then 3 else 3)))) else (if x<3180 then (if x<2800 then (if x<2776 then 2 else (if x<2788 then 3 else 3)) else (if x<3102 then 2 else (if x<3126 then 4 else 1))) else (if x<3256 then (if x<3192 then 4 else (if x<3244 then 1 else 1)) else (if x<3274 then 4 else (if x<3298 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1545 : Finset ℕ := ([1626,1678,1714,2710,2730,2776,2788,3126,3192,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1545 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1545 4 (fun x => (if x<2776 then (if x<1714 then (if x<1678 then 0 else 0) else (if x<2710 then 0 else (if x<2730 then 1 else 1))) else (if x<3192 then (if x<2788 then 1 else (if x<3126 then 1 else 2)) else (if x<3244 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1546 : Finset ℕ := ([1596,1614,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3102,3126,3180,3192,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1546 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1546 1614 4
  · have he : independentCachedBranchMembers1546.erase 1614=independentCachedBranchMembers1544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1544
  · have he : independentCachedBranchMembers1546.filter (independentCachedEdge 1614)=independentCachedBranchMembers1545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1545
def independentCachedBranchMembers1547 : Finset ℕ := ([1596,1650,1678,1748,2646,2730,2788,2800,3102,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1547 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1547 4 (fun x => (if x<2788 then (if x<1748 then (if x<1650 then 0 else (if x<1678 then 0 else 1)) else (if x<2646 then 0 else (if x<2730 then 2 else 1))) else (if x<3244 then (if x<2800 then 2 else (if x<3102 then 1 else 2)) else (if x<3256 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1548 : Finset ℕ := ([72,1596,1614,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3102,3126,3180,3192,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1548 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1548 72 4
  · have he : independentCachedBranchMembers1548.erase 72=independentCachedBranchMembers1546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1546
  · have he : independentCachedBranchMembers1548.filter (independentCachedEdge 72)=independentCachedBranchMembers1547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1547
def independentCachedBranchMembers1549 : Finset ℕ := ([1596,1614,1678,1702,1748,2730,2776,2800,3192,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1549 4 (fun x => (if x<2776 then (if x<1702 then (if x<1614 then 0 else (if x<1678 then 0 else 1)) else (if x<1748 then 0 else (if x<2730 then 0 else 1))) else (if x<3256 then (if x<2800 then 2 else (if x<3192 then 1 else 2)) else (if x<3274 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1550 : Finset ℕ := ([18,72,1596,1614,1626,1650,1678,1702,1714,1748,1768,2646,2710,2730,2764,2776,2788,2800,3102,3126,3180,3192,3244,3256,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1550 18 4
  · have he : independentCachedBranchMembers1550.erase 18=independentCachedBranchMembers1548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1548
  · have he : independentCachedBranchMembers1550.filter (independentCachedEdge 18)=independentCachedBranchMembers1549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1549
def independentCachedBranchMembers1551 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1642,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1551 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1551 2772 5
  · have he : independentCachedBranchMembers1551.erase 2772=independentCachedBranchMembers1543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1543
  · have he : independentCachedBranchMembers1551.filter (independentCachedEdge 2772)=independentCachedBranchMembers1550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1550
def independentCachedBranchMembers1552 : Finset ℕ := ([1596,1614,1650,1702,1748,1768,2650,2662,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1552 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1552 5 (fun x => (if x<2738 then (if x<1768 then (if x<1650 then (if x<1614 then 0 else 0) else (if x<1702 then 0 else (if x<1748 then 0 else 0))) else (if x<2702 then (if x<2650 then 0 else (if x<2662 then 1 else 1)) else (if x<2710 then 1 else (if x<2730 then 2 else 2)))) else (if x<3164 then (if x<2788 then (if x<2776 then 1 else 2) else (if x<3118 then 2 else (if x<3126 then 3 else 4))) else (if x<3252 then (if x<3192 then 3 else (if x<3244 then 4 else 4)) else (if x<3270 then 3 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1553 : Finset ℕ := ([1596,1614,1768,2662,2730,2738,2776,3118,3126,3164,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1553 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1553 4 (fun x => (if x<2738 then (if x<1768 then (if x<1614 then 0 else 0) else (if x<2662 then 0 else (if x<2730 then 1 else 1))) else (if x<3126 then (if x<2776 then 2 else (if x<3118 then 2 else 1)) else (if x<3164 then 2 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1554 : Finset ℕ := ([132,1596,1614,1650,1702,1748,1768,2650,2662,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1554 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1554 132 4
  · have he : independentCachedBranchMembers1554.erase 132=independentCachedBranchMembers1552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1552
  · have he : independentCachedBranchMembers1554.filter (independentCachedEdge 132)=independentCachedBranchMembers1553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1553
def independentCachedBranchMembers1555 : Finset ℕ := ([1596,1650,1748,2662,2702,2730,2788,3118,3244,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1555 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1555 4 (fun x => (if x<2730 then (if x<1748 then (if x<1650 then 0 else 0) else (if x<2662 then 0 else (if x<2702 then 1 else 1))) else (if x<3244 then (if x<2788 then 2 else (if x<3118 then 2 else 1)) else (if x<3270 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1556 : Finset ℕ := ([72,132,1596,1614,1650,1702,1748,1768,2650,2662,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1556 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1556 72 4
  · have he : independentCachedBranchMembers1556.erase 72=independentCachedBranchMembers1554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1554
  · have he : independentCachedBranchMembers1556.filter (independentCachedEdge 72)=independentCachedBranchMembers1555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1555
def independentCachedBranchMembers1557 : Finset ℕ := ([1614,1650,1748,1768,2650,2662,2710,2730,3118,3192,3252,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1557 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1557 4 (fun x => (if x<2710 then (if x<1768 then (if x<1650 then 0 else (if x<1748 then 0 else 0)) else (if x<2650 then 0 else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<2730 then 1 else (if x<3118 then 1 else 2)) else (if x<3252 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1558 : Finset ℕ := ([72,132,1596,1614,1650,1702,1740,1748,1768,2650,2662,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1558 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1558 1740 4
  · have he : independentCachedBranchMembers1558.erase 1740=independentCachedBranchMembers1556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1556
  · have he : independentCachedBranchMembers1558.filter (independentCachedEdge 1740)=independentCachedBranchMembers1557 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1557
def independentCachedBranchMembers1559 : Finset ℕ := ([1614,1650,1748,1768,2702,2738,2776,2788,3126,3164,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1559 4 (fun x => (if x<2776 then (if x<1768 then (if x<1650 then 0 else (if x<1748 then 0 else 0)) else (if x<2702 then 0 else (if x<2738 then 1 else 1))) else (if x<3164 then (if x<2788 then 1 else (if x<3126 then 1 else 2)) else (if x<3244 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1560 : Finset ℕ := ([72,132,1596,1614,1642,1650,1702,1740,1748,1768,2650,2662,2702,2710,2730,2738,2776,2788,3118,3126,3164,3192,3244,3252,3270,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1560 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1560 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1560 1642 4
  · have he : independentCachedBranchMembers1560.erase 1642=independentCachedBranchMembers1558 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1558
  · have he : independentCachedBranchMembers1560.filter (independentCachedEdge 1642)=independentCachedBranchMembers1559 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1559
def independentCachedBranchMembers1561 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1642,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,2620,2646,2650,2662,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1561 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1561 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1561 2714 5
  · have he : independentCachedBranchMembers1561.erase 2714=independentCachedBranchMembers1551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1551
  · have he : independentCachedBranchMembers1561.filter (independentCachedEdge 2714)=independentCachedBranchMembers1560 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1560
def independentCachedBranchMembers1562 : Finset ℕ := ([1596,1614,1650,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3102,3118,3164,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1562 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1562 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1562 5 (fun x => (if x<2702 then (if x<1752 then (if x<1650 then (if x<1614 then 0 else 0) else (if x<1702 then 0 else (if x<1748 then 0 else 0))) else (if x<2646 then (if x<1764 then 1 else (if x<1768 then 1 else 0)) else (if x<2650 then 2 else (if x<2662 then 1 else 1)))) else (if x<3164 then (if x<2800 then (if x<2738 then 2 else (if x<2764 then 2 else 1)) else (if x<3102 then 1 else (if x<3118 then 3 else 4))) else (if x<3256 then (if x<3180 then 4 else (if x<3252 then 3 else 3)) else (if x<3270 then 4 else (if x<3274 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1563 : Finset ℕ := ([1702,1748,1768,2650,2662,2764,2800,3118,3164,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1563 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1563 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1563 4 (fun x => (if x<2764 then (if x<1768 then (if x<1748 then 0 else 0) else (if x<2650 then 0 else (if x<2662 then 1 else 1))) else (if x<3164 then (if x<2800 then 1 else (if x<3118 then 1 else 2)) else (if x<3256 then 2 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1564 : Finset ℕ := ([1596,1614,1650,1686,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3102,3118,3164,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1564 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1564 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1564 1686 4
  · have he : independentCachedBranchMembers1564.erase 1686=independentCachedBranchMembers1562 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1562
  · have he : independentCachedBranchMembers1564.filter (independentCachedEdge 1686)=independentCachedBranchMembers1563 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1563
def independentCachedBranchMembers1565 : Finset ℕ := ([1596,1650,1702,1764,1768,2662,2738,2800,3118,3180,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1565 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1565 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1565 4 (fun x => (if x<2738 then (if x<1764 then (if x<1650 then 0 else (if x<1702 then 0 else 0)) else (if x<1768 then 1 else (if x<2662 then 0 else 1))) else (if x<3180 then (if x<2800 then 2 else (if x<3118 then 1 else 3)) else (if x<3252 then 2 else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1566 : Finset ℕ := ([222,1596,1614,1650,1686,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3102,3118,3164,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1566 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1566 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1566 222 4
  · have he : independentCachedBranchMembers1566.erase 222=independentCachedBranchMembers1564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1564
  · have he : independentCachedBranchMembers1566.filter (independentCachedEdge 222)=independentCachedBranchMembers1565 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1565
def independentCachedBranchMembers1567 : Finset ℕ := ([1596,1650,1748,1764,2646,2662,2702,2800,3102,3118,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1567 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1567 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1567 4 (fun x => (if x<2702 then (if x<1764 then (if x<1650 then 0 else (if x<1748 then 0 else 0)) else (if x<2646 then 1 else (if x<2662 then 2 else 1))) else (if x<3118 then (if x<2800 then 2 else (if x<3102 then 1 else 2)) else (if x<3256 then 3 else (if x<3270 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1568 : Finset ℕ := ([72,222,1596,1614,1650,1686,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3102,3118,3164,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1568 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1568 72 4
  · have he : independentCachedBranchMembers1568.erase 72=independentCachedBranchMembers1566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1566
  · have he : independentCachedBranchMembers1568.filter (independentCachedEdge 72)=independentCachedBranchMembers1567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1567
def independentCachedBranchMembers1569 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1642,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,2620,2646,2650,2662,2674,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1569 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1569 2674 5
  · have he : independentCachedBranchMembers1569.erase 2674=independentCachedBranchMembers1561 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1561
  · have he : independentCachedBranchMembers1569.filter (independentCachedEdge 2674)=independentCachedBranchMembers1568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1568
def independentCachedBranchMembers1570 : Finset ℕ := ([1596,1614,1650,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3126,3130,3188,3192,3228,3244,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1570 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1570 5 (fun x => (if x<2702 then (if x<1752 then (if x<1650 then (if x<1614 then 0 else 0) else (if x<1702 then 0 else (if x<1748 then 0 else 0))) else (if x<2646 then (if x<1764 then 1 else (if x<1768 then 1 else 0)) else (if x<2650 then 2 else (if x<2662 then 1 else 1)))) else (if x<3188 then (if x<2800 then (if x<2738 then 2 else (if x<2764 then 2 else 1)) else (if x<3126 then 1 else (if x<3130 then 3 else 4))) else (if x<3244 then (if x<3192 then 4 else (if x<3228 then 3 else 3)) else (if x<3282 then 4 else (if x<3298 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1571 : Finset ℕ := ([1702,1748,1768,2650,2662,2764,2800,3130,3188,3244,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1571 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1571 4 (fun x => (if x<2764 then (if x<1768 then (if x<1748 then 0 else 0) else (if x<2650 then 0 else (if x<2662 then 1 else 1))) else (if x<3188 then (if x<2800 then 1 else (if x<3130 then 1 else 2)) else (if x<3244 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1572 : Finset ℕ := ([1596,1614,1650,1686,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3126,3130,3188,3192,3228,3244,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1572 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1572 1686 4
  · have he : independentCachedBranchMembers1572.erase 1686=independentCachedBranchMembers1570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1570
  · have he : independentCachedBranchMembers1572.filter (independentCachedEdge 1686)=independentCachedBranchMembers1571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1571
def independentCachedBranchMembers1573 : Finset ℕ := ([1596,1614,1752,1768,2646,2662,2738,2800,3126,3188,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1573 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1573 4 (fun x => (if x<2738 then (if x<1768 then (if x<1614 then 0 else (if x<1752 then 0 else 0)) else (if x<2646 then 1 else (if x<2662 then 1 else 2))) else (if x<3188 then (if x<2800 then 2 else (if x<3126 then 1 else 2)) else (if x<3282 then 3 else (if x<3298 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1574 : Finset ℕ := ([132,1596,1614,1650,1686,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3126,3130,3188,3192,3228,3244,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1574 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1574 132 4
  · have he : independentCachedBranchMembers1574.erase 132=independentCachedBranchMembers1572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1572
  · have he : independentCachedBranchMembers1574.filter (independentCachedEdge 132)=independentCachedBranchMembers1573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1573
def independentCachedBranchMembers1575 : Finset ℕ := ([1596,1614,1702,1748,1752,2662,2702,2800,3188,3192,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1575 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1575 4 (fun x => (if x<2702 then (if x<1748 then (if x<1614 then 0 else (if x<1702 then 0 else 0)) else (if x<1752 then 0 else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<2800 then 2 else (if x<3188 then 1 else 2)) else (if x<3228 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1576 : Finset ℕ := ([18,132,1596,1614,1650,1686,1702,1748,1752,1764,1768,2646,2650,2662,2702,2738,2764,2800,3126,3130,3188,3192,3228,3244,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1576 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1576 18 4
  · have he : independentCachedBranchMembers1576.erase 18=independentCachedBranchMembers1574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1574
  · have he : independentCachedBranchMembers1576.filter (independentCachedEdge 18)=independentCachedBranchMembers1575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1575
def independentCachedBranchMembers1577 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1642,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,2620,2638,2646,2650,2662,2674,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1577 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1577 2638 5
  · have he : independentCachedBranchMembers1577.erase 2638=independentCachedBranchMembers1569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1569
  · have he : independentCachedBranchMembers1577.filter (independentCachedEdge 2638)=independentCachedBranchMembers1576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1576
def independentCachedBranchMembers1578 : Finset ℕ := ([222,1614,1650,1678,1714,1748,1752,1764,1768,2620,2646,2650,2662,2710,2714,2730,2764,2800,3126,3130,3164,3180,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1578 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1578 5 (fun x => (if x<2710 then (if x<1752 then (if x<1678 then (if x<1614 then 0 else (if x<1650 then 0 else 1)) else (if x<1714 then 2 else (if x<1748 then 2 else 0))) else (if x<2620 then (if x<1764 then 1 else (if x<1768 then 1 else 2)) else (if x<2650 then (if x<2646 then 3 else 0) else (if x<2662 then 1 else 1)))) else (if x<3130 then (if x<2764 then (if x<2714 then 2 else (if x<2730 then 3 else 2)) else (if x<2800 then 0 else (if x<3126 then 1 else 4))) else (if x<3228 then (if x<3164 then 3 else (if x<3180 then 0 else 3)) else (if x<3270 then (if x<3244 then 3 else 4) else (if x<3274 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1579 : Finset ℕ := ([1614,1678,1748,1752,2620,2662,2730,2800,3164,3228,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1579 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1579 4 (fun x => (if x<2730 then (if x<1752 then (if x<1678 then 0 else (if x<1748 then 1 else 0)) else (if x<2620 then 1 else (if x<2662 then 2 else 2))) else (if x<3228 then (if x<2800 then 2 else (if x<3164 then 0 else 3)) else (if x<3270 then 1 else (if x<3274 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1580 : Finset ℕ := ([18,222,1614,1650,1678,1714,1748,1752,1764,1768,2620,2646,2650,2662,2710,2714,2730,2764,2800,3126,3130,3164,3180,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1580 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1580 18 4
  · have he : independentCachedBranchMembers1580.erase 18=independentCachedBranchMembers1578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1578
  · have he : independentCachedBranchMembers1580.filter (independentCachedEdge 18)=independentCachedBranchMembers1579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1579
def independentCachedBranchMembers1581 : Finset ℕ := ([1614,1714,1752,1768,2620,2662,2714,2730,2800,3126,3164,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1581 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1581 4 (fun x => (if x<2714 then (if x<1768 then (if x<1714 then 0 else (if x<1752 then 1 else 0)) else (if x<2620 then 1 else (if x<2662 then 2 else 0))) else (if x<3126 then (if x<2730 then 2 else (if x<2800 then 1 else 0)) else (if x<3180 then (if x<3164 then 3 else 3) else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1582 : Finset ℕ := ([1714,1752,2662,2730,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1582 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1582 3 (fun x => (if x<2730 then (if x<1752 then 0 else (if x<2662 then 0 else 1)) else (if x<3180 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1583 : Finset ℕ := ([1614,1714,1752,1768,2620,2646,2662,2714,2730,2800,3126,3164,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1583 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1583 2646 3
  · have he : independentCachedBranchMembers1583.erase 2646=independentCachedBranchMembers1581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1581
  · have he : independentCachedBranchMembers1583.filter (independentCachedEdge 2646)=independentCachedBranchMembers1582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1582
def independentCachedBranchMembers1584 : Finset ℕ := ([18,132,222,1614,1650,1678,1714,1748,1752,1764,1768,2620,2646,2650,2662,2710,2714,2730,2764,2800,3126,3130,3164,3180,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1584 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1584 132 4
  · have he : independentCachedBranchMembers1584.erase 132=independentCachedBranchMembers1580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1580
  · have he : independentCachedBranchMembers1584.filter (independentCachedEdge 132)=independentCachedBranchMembers1583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1583
def independentCachedBranchMembers1585 : Finset ℕ := ([1650,1678,1748,1764,2620,2662,2730,2800,3130,3228,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1585 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1585 4 (fun x => (if x<2730 then (if x<1764 then (if x<1678 then 0 else (if x<1748 then 1 else 0)) else (if x<2620 then 1 else (if x<2662 then 2 else 2))) else (if x<3228 then (if x<2800 then 2 else (if x<3130 then 0 else 3)) else (if x<3244 then 3 else (if x<3270 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1586 : Finset ℕ := ([1650,1748,2662,2730,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1586 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1586 3 (fun x => (if x<2730 then (if x<1748 then 0 else (if x<2662 then 0 else 1)) else (if x<3244 then 1 else (if x<3270 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1587 : Finset ℕ := ([1650,1678,1748,1764,2620,2662,2714,2730,2800,3130,3228,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1587 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1587 2714 3
  · have he : independentCachedBranchMembers1587.erase 2714=independentCachedBranchMembers1585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1585
  · have he : independentCachedBranchMembers1587.filter (independentCachedEdge 2714)=independentCachedBranchMembers1586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1586
def independentCachedBranchMembers1588 : Finset ℕ := ([1678,1764,2662,2730,3130,3228] : List ℕ).toFinset
theorem independentCachedBranchBound1588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1588 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1588 3 (fun x => (if x<2730 then (if x<1764 then 0 else (if x<2662 then 0 else 1)) else (if x<3130 then 1 else (if x<3228 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1589 : Finset ℕ := ([1650,1678,1748,1764,2620,2646,2662,2714,2730,2800,3130,3228,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1589 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1589 2646 3
  · have he : independentCachedBranchMembers1589.erase 2646=independentCachedBranchMembers1587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1587
  · have he : independentCachedBranchMembers1589.filter (independentCachedEdge 2646)=independentCachedBranchMembers1588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1588
def independentCachedBranchMembers1590 : Finset ℕ := ([18,72,132,222,1614,1650,1678,1714,1748,1752,1764,1768,2620,2646,2650,2662,2710,2714,2730,2764,2800,3126,3130,3164,3180,3228,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound1590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1590 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1590 72 4
  · have he : independentCachedBranchMembers1590.erase 72=independentCachedBranchMembers1584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1584
  · have he : independentCachedBranchMembers1590.filter (independentCachedEdge 72)=independentCachedBranchMembers1589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1589
def independentCachedBranchMembers1591 : Finset ℕ := ([18,72,132,222,1596,1614,1626,1642,1650,1678,1686,1702,1714,1740,1748,1752,1764,1768,1776,2620,2638,2646,2650,2662,2674,2702,2710,2714,2730,2738,2764,2772,2776,2788,2792,2800,3102,3118,3126,3130,3164,3180,3188,3192,3228,3244,3252,3256,3270,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1591 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1591 1776 5
  · have he : independentCachedBranchMembers1591.erase 1776=independentCachedBranchMembers1577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1577
  · have he : independentCachedBranchMembers1591.filter (independentCachedEdge 1776)=independentCachedBranchMembers1590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1590
def independentCachedBranchMembers1592 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1592 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1592 3132 6
  · have he : independentCachedBranchMembers1592.erase 3132=independentCachedBranchMembers1498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1498
  · have he : independentCachedBranchMembers1592.filter (independentCachedEdge 3132)=independentCachedBranchMembers1591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1591
def independentCachedBranchMembers1593 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2680,2740,2764,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1593 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1593 6 (fun x => (if x<2740 then (if x<1692 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1642 then (if x<1628 then 1 else 2) else (if x<1650 then 1 else 2))) else (if x<1738 then (if x<1714 then (if x<1702 then 3 else 1) else (if x<1734 then 3 else 2)) else (if x<1768 then (if x<1764 then 3 else 3) else (if x<1776 then 2 else (if x<2680 then 1 else 0))))) else (if x<3214 then (if x<3162 then (if x<3130 then (if x<2764 then 0 else 0) else (if x<3150 then 4 else 4)) else (if x<3188 then (if x<3180 then 5 else 5) else (if x<3192 then 4 else 1))) else (if x<3256 then (if x<3244 then (if x<3222 then 5 else 4) else (if x<3252 then 4 else 1)) else (if x<3284 then (if x<3276 then 5 else 2) else (if x<3288 then 5 else (if x<3298 then 4 else 1)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1594 : Finset ℕ := ([132,252,1628,1642,1692,1734,1764,1776,2680,3130,3188,3222,3252,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1594 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1594 5 (fun x => (if x<1776 then (if x<1642 then (if x<252 then 0 else (if x<1628 then 0 else 1)) else (if x<1734 then (if x<1692 then 1 else 0) else (if x<1764 then 1 else 0))) else (if x<3222 then (if x<3130 then (if x<2680 then 1 else 1) else (if x<3188 then 2 else 2)) else (if x<3276 then (if x<3252 then 2 else 0) else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1595 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2680,2740,2764,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1595 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1595 3126 5
  · have he : independentCachedBranchMembers1595.erase 3126=independentCachedBranchMembers1593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1593
  · have he : independentCachedBranchMembers1595.filter (independentCachedEdge 3126)=independentCachedBranchMembers1594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1594
def independentCachedBranchMembers1596 : Finset ℕ := ([48,72,132,252,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1596 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1596 5 (fun x => (if x<3192 then (if x<3130 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else (if x<3126 then 0 else 1))) else (if x<3162 then (if x<3150 then 2 else 1) else (if x<3180 then 3 else (if x<3188 then 2 else 3)))) else (if x<3256 then (if x<3222 then (if x<3214 then 0 else 2) else (if x<3244 then 3 else (if x<3252 then 1 else 0))) else (if x<3284 then (if x<3276 then 3 else 0) else (if x<3288 then 1 else (if x<3298 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1597 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2680,2740,2764,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1597 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1597 2786 5
  · have he : independentCachedBranchMembers1597.erase 2786=independentCachedBranchMembers1595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1595
  · have he : independentCachedBranchMembers1597.filter (independentCachedEdge 2786)=independentCachedBranchMembers1596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1596
def independentCachedBranchMembers1598 : Finset ℕ := ([48,132,1596,1642,1650,1714,1734,1764,2680,2764,3130,3150,3180,3188,3214,3222,3244,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1598 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1598 5 (fun x => (if x<3130 then (if x<1714 then (if x<1596 then (if x<132 then 0 else 0) else (if x<1642 then 1 else (if x<1650 then 1 else 0))) else (if x<1764 then (if x<1734 then 1 else 0) else (if x<2680 then 1 else (if x<2764 then 0 else 0)))) else (if x<3222 then (if x<3180 then (if x<3150 then 0 else 2) else (if x<3188 then 1 else (if x<3214 then 2 else 0))) else (if x<3252 then (if x<3244 then 2 else 2) else (if x<3288 then 1 else (if x<3298 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1599 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2680,2740,2764,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1599 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1599 2776 5
  · have he : independentCachedBranchMembers1599.erase 2776=independentCachedBranchMembers1597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1597
  · have he : independentCachedBranchMembers1599.filter (independentCachedEdge 2776)=independentCachedBranchMembers1598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1598
def independentCachedBranchMembers1600 : Finset ℕ := ([72,252,1596,1628,1642,1714,1764,1768,2680,2764,3126,3130,3162,3180,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1600 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1600 5 (fun x => (if x<3126 then (if x<1714 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1628 then 1 else (if x<1642 then 0 else 1))) else (if x<1768 then (if x<1764 then 1 else 1) else (if x<2680 then 0 else (if x<2764 then 0 else 0)))) else (if x<3252 then (if x<3162 then (if x<3130 then 2 else 1) else (if x<3180 then 2 else (if x<3214 then 0 else 2))) else (if x<3284 then (if x<3256 then 1 else 2) else (if x<3288 then 2 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1601 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2680,2702,2740,2764,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1601 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1601 2702 5
  · have he : independentCachedBranchMembers1601.erase 2702=independentCachedBranchMembers1599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1599
  · have he : independentCachedBranchMembers1601.filter (independentCachedEdge 2702)=independentCachedBranchMembers1600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1600
def independentCachedBranchMembers1602 : Finset ℕ := ([48,132,1650,1692,1702,1734,1738,1776,2680,2764,3126,3130,3162,3180,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1602 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1602 5 (fun x => (if x<3126 then (if x<1734 then (if x<1650 then (if x<132 then 0 else 0) else (if x<1692 then 0 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1738 then 0 else 1) else (if x<2680 then 1 else (if x<2764 then 0 else 0)))) else (if x<3252 then (if x<3162 then (if x<3130 then 2 else 0) else (if x<3180 then 2 else (if x<3214 then 2 else 0))) else (if x<3284 then (if x<3256 then 1 else 2) else (if x<3288 then 2 else (if x<3298 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1603 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2668,2680,2702,2740,2764,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1603 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1603 2668 5
  · have he : independentCachedBranchMembers1603.erase 2668=independentCachedBranchMembers1601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1601
  · have he : independentCachedBranchMembers1603.filter (independentCachedEdge 2668)=independentCachedBranchMembers1602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1602
def independentCachedBranchMembers1604 : Finset ℕ := ([72,252,1628,1692,1702,1738,1768,1776,2680,2764,3130,3150,3180,3188,3214,3222,3244,3252,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1604 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1604 5 (fun x => (if x<3130 then (if x<1738 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1692 then 0 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1768 then 1 else 0) else (if x<2680 then 1 else (if x<2764 then 0 else 0)))) else (if x<3222 then (if x<3180 then (if x<3150 then 2 else 2) else (if x<3188 then 0 else (if x<3214 then 2 else 1))) else (if x<3252 then (if x<3244 then 2 else 2) else (if x<3288 then 1 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1605 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2618,2668,2680,2702,2740,2764,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1605 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1605 2618 5
  · have he : independentCachedBranchMembers1605.erase 2618=independentCachedBranchMembers1603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1603
  · have he : independentCachedBranchMembers1605.filter (independentCachedEdge 2618)=independentCachedBranchMembers1604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1604
def independentCachedBranchMembers1606 : Finset ℕ := ([48,72,1596,1650,1702,1714,1738,1768,2618,2740,2764,2776,3126,3150,3162,3180,3192,3214,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1606 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1606 5 (fun x => (if x<2776 then (if x<1714 then (if x<1596 then (if x<72 then 0 else 0) else (if x<1650 then 1 else (if x<1702 then 1 else 1))) else (if x<2618 then (if x<1738 then 0 else (if x<1768 then 0 else 1)) else (if x<2740 then 2 else (if x<2764 then 0 else 0)))) else (if x<3192 then (if x<3150 then (if x<3126 then 2 else 0) else (if x<3162 then 0 else (if x<3180 then 2 else 3))) else (if x<3256 then (if x<3214 then 1 else (if x<3244 then 3 else 1)) else (if x<3284 then 2 else (if x<3298 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1607 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2618,2668,2680,2702,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1607 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1607 2772 5
  · have he : independentCachedBranchMembers1607.erase 2772=independentCachedBranchMembers1605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1605
  · have he : independentCachedBranchMembers1607.filter (independentCachedEdge 2772)=independentCachedBranchMembers1606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1606
def independentCachedBranchMembers1608 : Finset ℕ := ([48,72,1628,1642,1714,1734,1738,1776,2668,2702,2740,2764,3126,3130,3150,3188,3192,3222,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1608 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1608 5 (fun x => (if x<2764 then (if x<1734 then (if x<1628 then (if x<72 then 0 else 0) else (if x<1642 then 1 else (if x<1714 then 1 else 0))) else (if x<2668 then (if x<1738 then 1 else (if x<1776 then 0 else 1)) else (if x<2702 then 2 else (if x<2740 then 2 else 0)))) else (if x<3192 then (if x<3130 then (if x<3126 then 0 else 0) else (if x<3150 then 3 else (if x<3188 then 0 else 2))) else (if x<3284 then (if x<3222 then 1 else (if x<3244 then 2 else 2)) else (if x<3288 then 1 else (if x<3298 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1609 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2618,2668,2680,2702,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1609 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1609 2732 5
  · have he : independentCachedBranchMembers1609.erase 2732=independentCachedBranchMembers1607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1607
  · have he : independentCachedBranchMembers1609.filter (independentCachedEdge 2732)=independentCachedBranchMembers1608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1608
def independentCachedBranchMembers1610 : Finset ℕ := ([132,252,1596,1650,1692,1702,1764,1768,2668,2702,2740,2764,3126,3130,3150,3188,3192,3222,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1610 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1610 5 (fun x => (if x<2764 then (if x<1702 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1650 then 1 else (if x<1692 then 1 else 0))) else (if x<2668 then (if x<1764 then 1 else (if x<1768 then 0 else 1)) else (if x<2702 then 2 else (if x<2740 then 2 else 0)))) else (if x<3192 then (if x<3130 then (if x<3126 then 0 else 1) else (if x<3150 then 3 else (if x<3188 then 2 else 2))) else (if x<3284 then (if x<3222 then 1 else (if x<3244 then 2 else 0)) else (if x<3288 then 0 else (if x<3298 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1611 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2618,2638,2668,2680,2702,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1611 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1611 2638 5
  · have he : independentCachedBranchMembers1611.erase 2638=independentCachedBranchMembers1609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1609
  · have he : independentCachedBranchMembers1611.filter (independentCachedEdge 2638)=independentCachedBranchMembers1610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1610
def independentCachedBranchMembers1612 : Finset ℕ := ([132,252,1628,1642,1692,1734,1764,1776,2618,2740,2764,2776,3126,3150,3162,3180,3192,3214,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1612 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1612 5 (fun x => (if x<2776 then (if x<1734 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1692 then 1 else 0))) else (if x<2618 then (if x<1764 then 1 else (if x<1776 then 0 else 1)) else (if x<2740 then 2 else (if x<2764 then 0 else 0)))) else (if x<3192 then (if x<3150 then (if x<3126 then 2 else 2) else (if x<3162 then 1 else (if x<3180 then 2 else 3))) else (if x<3256 then (if x<3214 then 1 else (if x<3244 then 3 else 0)) else (if x<3284 then 2 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1613 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2614,2618,2638,2668,2680,2702,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1613 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1613 2614 5
  · have he : independentCachedBranchMembers1613.erase 2614=independentCachedBranchMembers1611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1611
  · have he : independentCachedBranchMembers1613.filter (independentCachedEdge 2614)=independentCachedBranchMembers1612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1612
def independentCachedBranchMembers1614 : Finset ℕ := ([48,252,1596,1628,1650,1738,1764,1776,2614,2668,2680,2702,2740,2772,3130,3150,3162,3188,3222,3244,3256,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1614 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1614 5 (fun x => (if x<2740 then (if x<1764 then (if x<1628 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1650 then 1 else (if x<1738 then 1 else 1))) else (if x<2668 then (if x<1776 then 1 else (if x<2614 then 0 else 2)) else (if x<2680 then 2 else (if x<2702 then 0 else 2)))) else (if x<3222 then (if x<3150 then (if x<2772 then 0 else (if x<3130 then 2 else 3)) else (if x<3162 then 3 else (if x<3188 then 1 else 0))) else (if x<3276 then (if x<3244 then 2 else (if x<3256 then 3 else 0)) else (if x<3288 then 1 else (if x<3298 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1615 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2614,2618,2638,2668,2680,2702,2710,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1615 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1615 2710 5
  · have he : independentCachedBranchMembers1615.erase 2710=independentCachedBranchMembers1613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1613
  · have he : independentCachedBranchMembers1615.filter (independentCachedEdge 2710)=independentCachedBranchMembers1614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1614
def independentCachedBranchMembers1616 : Finset ℕ := ([48,252,1596,1692,1714,1734,1768,1776,2618,2638,2680,2732,2740,2776,3126,3162,3180,3188,3214,3222,3256,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1616 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1616 5 (fun x => (if x<2740 then (if x<1768 then (if x<1692 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1714 then 1 else (if x<1734 then 1 else 1))) else (if x<2638 then (if x<1776 then 1 else (if x<2618 then 0 else 2)) else (if x<2680 then 2 else (if x<2732 then 0 else 2)))) else (if x<3214 then (if x<3162 then (if x<2776 then 0 else (if x<3126 then 2 else 3)) else (if x<3180 then 2 else (if x<3188 then 3 else 0))) else (if x<3276 then (if x<3222 then 3 else (if x<3256 then 1 else 0)) else (if x<3284 then 1 else (if x<3298 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1617 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2614,2618,2638,2650,2668,2680,2702,2710,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1617 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1617 2650 5
  · have he : independentCachedBranchMembers1617.erase 2650=independentCachedBranchMembers1615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1615
  · have he : independentCachedBranchMembers1617.filter (independentCachedEdge 2650)=independentCachedBranchMembers1616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1616
def independentCachedBranchMembers1618 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1702,1734,1768,1776,2618,2668,2702,2776,3126,3150,3192,3244,3252,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1618 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1618 5 (fun x => (if x<2618 then (if x<1642 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1596 then 0 else (if x<1628 then 1 else 2))) else (if x<1734 then (if x<1650 then 1 else (if x<1702 then 2 else 1)) else (if x<1768 then 2 else (if x<1776 then 2 else 1)))) else (if x<3192 then (if x<2776 then (if x<2668 then 3 else (if x<2702 then 3 else 3)) else (if x<3126 then 3 else (if x<3150 then 4 else 4))) else (if x<3276 then (if x<3244 then 0 else (if x<3252 then 4 else 0)) else (if x<3284 then 0 else (if x<3298 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1619 : Finset ℕ := ([48,252,1596,1628,1650,1776,2668,2702,3150,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1619 4 (fun x => (if x<2668 then (if x<1628 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1650 then 1 else (if x<1776 then 1 else 0))) else (if x<3244 then (if x<2702 then 2 else (if x<3150 then 2 else 2)) else (if x<3276 then 2 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1620 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1702,1734,1768,1776,2618,2668,2702,2710,2776,3126,3150,3192,3244,3252,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1620 2710 4
  · have he : independentCachedBranchMembers1620.erase 2710=independentCachedBranchMembers1618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1618
  · have he : independentCachedBranchMembers1620.filter (independentCachedEdge 2710)=independentCachedBranchMembers1619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1619
def independentCachedBranchMembers1621 : Finset ℕ := ([48,252,1596,1734,1768,1776,2618,2776,3126,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1621 4 (fun x => (if x<2618 then (if x<1734 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1768 then 1 else (if x<1776 then 1 else 0))) else (if x<3276 then (if x<2776 then 2 else (if x<3126 then 2 else 2)) else (if x<3284 then 1 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1622 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1702,1734,1768,1776,2618,2650,2668,2702,2710,2776,3126,3150,3192,3244,3252,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1622 2650 4
  · have he : independentCachedBranchMembers1622.erase 2650=independentCachedBranchMembers1620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1620
  · have he : independentCachedBranchMembers1622.filter (independentCachedEdge 2650)=independentCachedBranchMembers1621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1621
def independentCachedBranchMembers1623 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2614,2618,2638,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1623 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1623 2714 5
  · have he : independentCachedBranchMembers1623.erase 2714=independentCachedBranchMembers1617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1617
  · have he : independentCachedBranchMembers1623.filter (independentCachedEdge 2714)=independentCachedBranchMembers1622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1622
def independentCachedBranchMembers1624 : Finset ℕ := ([48,72,132,252,1596,1642,1692,1702,1714,1738,1764,1776,2614,2638,2732,2772,3130,3180,3192,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1624 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1624 5 (fun x => (if x<2614 then (if x<1692 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1596 then 0 else (if x<1642 then 1 else 1))) else (if x<1738 then (if x<1702 then 2 else (if x<1714 then 1 else 2)) else (if x<1764 then 2 else (if x<1776 then 2 else 1)))) else (if x<3192 then (if x<2772 then (if x<2638 then 3 else (if x<2732 then 3 else 3)) else (if x<3130 then 3 else (if x<3180 then 4 else 4))) else (if x<3276 then (if x<3214 then 0 else (if x<3252 then 4 else 0)) else (if x<3288 then 0 else (if x<3298 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1625 : Finset ℕ := ([48,252,1596,1738,1764,1776,2614,2772,3130,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1625 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1625 4 (fun x => (if x<2614 then (if x<1738 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1764 then 1 else (if x<1776 then 1 else 0))) else (if x<3276 then (if x<2772 then 2 else (if x<3130 then 2 else 2)) else (if x<3288 then 1 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1626 : Finset ℕ := ([48,72,132,252,1596,1642,1692,1702,1714,1738,1764,1776,2614,2638,2710,2732,2772,3130,3180,3192,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1626 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1626 2710 4
  · have he : independentCachedBranchMembers1626.erase 2710=independentCachedBranchMembers1624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1624
  · have he : independentCachedBranchMembers1626.filter (independentCachedEdge 2710)=independentCachedBranchMembers1625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1625
def independentCachedBranchMembers1627 : Finset ℕ := ([48,252,1596,1692,1714,1776,2638,2732,3180,3214,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1627 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1627 4 (fun x => (if x<2638 then (if x<1692 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1714 then 1 else (if x<1776 then 1 else 0))) else (if x<3214 then (if x<2732 then 2 else (if x<3180 then 2 else 2)) else (if x<3276 then 2 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1628 : Finset ℕ := ([48,72,132,252,1596,1642,1692,1702,1714,1738,1764,1776,2614,2638,2650,2710,2732,2772,3130,3180,3192,3214,3252,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1628 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1628 2650 4
  · have he : independentCachedBranchMembers1628.erase 2650=independentCachedBranchMembers1626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1626
  · have he : independentCachedBranchMembers1628.filter (independentCachedEdge 2650)=independentCachedBranchMembers1627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1627
def independentCachedBranchMembers1629 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1629 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1629 2646 5
  · have he : independentCachedBranchMembers1629.erase 2646=independentCachedBranchMembers1623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1623
  · have he : independentCachedBranchMembers1629.filter (independentCachedEdge 2646)=independentCachedBranchMembers1628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1628
def independentCachedBranchMembers1630 : Finset ℕ := ([48,72,132,1596,1650,1714,1734,1738,1776,2618,2638,2680,2702,2740,2764,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1630 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1630 5 (fun x => (if x<2702 then (if x<1734 then (if x<1596 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1650 then 1 else (if x<1714 then 1 else 2))) else (if x<2618 then (if x<1738 then 2 else (if x<1776 then 3 else 3)) else (if x<2638 then 1 else (if x<2680 then 2 else 0)))) else (if x<3188 then (if x<3126 then (if x<2740 then 3 else (if x<2764 then 0 else 0)) else (if x<3130 then 1 else (if x<3150 then 4 else 3))) else (if x<3252 then (if x<3192 then 3 else (if x<3214 then 1 else 4)) else (if x<3256 then 4 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1631 : Finset ℕ := ([132,1734,1776,2618,2740,2764,3126,3150,3192,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1631 4 (fun x => (if x<2764 then (if x<1776 then (if x<1734 then 0 else 0) else (if x<2618 then 1 else (if x<2740 then 0 else 1))) else (if x<3192 then (if x<3126 then 2 else (if x<3150 then 2 else 1)) else (if x<3214 then 0 else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1632 : Finset ℕ := ([48,72,132,1596,1650,1714,1734,1738,1776,2614,2618,2638,2680,2702,2740,2764,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1632 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1632 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1632 2614 4
  · have he : independentCachedBranchMembers1632.erase 2614=independentCachedBranchMembers1630 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1630
  · have he : independentCachedBranchMembers1632.filter (independentCachedEdge 2614)=independentCachedBranchMembers1631 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1631
def independentCachedBranchMembers1633 : Finset ℕ := ([1650,1714,1734,1738,2614,2618,2638,2702,3126,3130,3150,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1633 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1633 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1633 4 (fun x => (if x<2638 then (if x<1738 then (if x<1714 then 0 else (if x<1734 then 1 else 0)) else (if x<2614 then 1 else (if x<2618 then 1 else 0))) else (if x<3130 then (if x<2702 then 1 else (if x<3126 then 0 else 2)) else (if x<3150 then 3 else (if x<3214 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1634 : Finset ℕ := ([48,72,132,252,1596,1650,1714,1734,1738,1776,2614,2618,2638,2680,2702,2740,2764,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1634 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1634 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1634 252 4
  · have he : independentCachedBranchMembers1634.erase 252=independentCachedBranchMembers1632 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1632
  · have he : independentCachedBranchMembers1634.filter (independentCachedEdge 252)=independentCachedBranchMembers1633 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1633
def independentCachedBranchMembers1635 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1635 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1635 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1635 1746 5
  · have he : independentCachedBranchMembers1635.erase 1746=independentCachedBranchMembers1629 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1629
  · have he : independentCachedBranchMembers1635.filter (independentCachedEdge 1746)=independentCachedBranchMembers1634 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1634
def independentCachedBranchMembers1636 : Finset ℕ := ([48,252,1596,1642,1650,1702,1714,1764,1768,2618,2680,2732,2740,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1636 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1636 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1636 5 (fun x => (if x<2732 then (if x<1702 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1642 then 0 else (if x<1650 then 1 else 2))) else (if x<1768 then (if x<1714 then 1 else (if x<1764 then 3 else 2)) else (if x<2618 then 3 else (if x<2680 then 2 else 0)))) else (if x<3188 then (if x<3126 then (if x<2740 then 2 else 0) else (if x<3130 then 3 else (if x<3180 then 4 else 3))) else (if x<3252 then (if x<3192 then 0 else (if x<3244 then 1 else 4)) else (if x<3256 then 1 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1637 : Finset ℕ := ([48,252,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1637 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1637 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1637 4 (fun x => (if x<3188 then (if x<3126 then (if x<252 then 0 else 0) else (if x<3130 then 1 else (if x<3180 then 2 else 1))) else (if x<3252 then (if x<3192 then 0 else (if x<3244 then 3 else 2)) else (if x<3256 then 3 else (if x<3298 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1638 : Finset ℕ := ([48,252,1596,1642,1650,1702,1714,1764,1768,2618,2680,2732,2740,2786,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1638 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1638 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1638 2786 4
  · have he : independentCachedBranchMembers1638.erase 2786=independentCachedBranchMembers1636 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1636
  · have he : independentCachedBranchMembers1638.filter (independentCachedEdge 2786)=independentCachedBranchMembers1637 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1637
def independentCachedBranchMembers1639 : Finset ℕ := ([48,1650,1702,2680,2732,3126,3130,3180,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1639 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1639 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1639 4 (fun x => (if x<3126 then (if x<1702 then (if x<1650 then 0 else 0) else (if x<2680 then 1 else (if x<2732 then 0 else 1))) else (if x<3252 then (if x<3130 then 2 else (if x<3180 then 0 else 2)) else (if x<3256 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1640 : Finset ℕ := ([48,252,1596,1642,1650,1702,1714,1764,1768,2618,2668,2680,2732,2740,2786,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1640 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1640 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1640 2668 4
  · have he : independentCachedBranchMembers1640.erase 2668=independentCachedBranchMembers1638 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1638
  · have he : independentCachedBranchMembers1640.filter (independentCachedEdge 2668)=independentCachedBranchMembers1639 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1639
def independentCachedBranchMembers1641 : Finset ℕ := ([252,1642,1764,2618,2740,3126,3180,3192,3244,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1641 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1641 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1641 4 (fun x => (if x<3126 then (if x<1764 then (if x<1642 then 0 else 1) else (if x<2618 then 0 else (if x<2740 then 1 else 0))) else (if x<3244 then (if x<3180 then 2 else (if x<3192 then 2 else 1)) else (if x<3256 then 0 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1642 : Finset ℕ := ([48,252,1596,1642,1650,1702,1714,1764,1768,2614,2618,2668,2680,2732,2740,2786,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1642 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1642 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1642 2614 4
  · have he : independentCachedBranchMembers1642.erase 2614=independentCachedBranchMembers1640 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1640
  · have he : independentCachedBranchMembers1642.filter (independentCachedEdge 2614)=independentCachedBranchMembers1641 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1641
def independentCachedBranchMembers1643 : Finset ℕ := ([1650,1714,1764,1768,2614,2618,2668,2732,3126,3130,3180,3244] : List ℕ).toFinset
theorem independentCachedBranchBound1643 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1643 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1643 4 (fun x => (if x<2668 then (if x<1768 then (if x<1714 then 0 else (if x<1764 then 1 else 0)) else (if x<2614 then 1 else (if x<2618 then 1 else 0))) else (if x<3130 then (if x<2732 then 1 else (if x<3126 then 0 else 2)) else (if x<3180 then 3 else (if x<3244 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1644 : Finset ℕ := ([48,252,1596,1642,1650,1702,1714,1764,1768,1776,2614,2618,2668,2680,2732,2740,2786,3126,3130,3180,3188,3192,3244,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1644 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1644 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1644 1776 4
  · have he : independentCachedBranchMembers1644.erase 1776=independentCachedBranchMembers1642 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1642
  · have he : independentCachedBranchMembers1644.filter (independentCachedEdge 1776)=independentCachedBranchMembers1643 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1643
def independentCachedBranchMembers1645 : Finset ℕ := ([48,72,132,222,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1645 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1645 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1645 222 5
  · have he : independentCachedBranchMembers1645.erase 222=independentCachedBranchMembers1635 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1635
  · have he : independentCachedBranchMembers1645.filter (independentCachedEdge 222)=independentCachedBranchMembers1644 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1644
def independentCachedBranchMembers1646 : Finset ℕ := ([48,252,1596,1628,1642,1692,1702,1734,1738,1776,2638,2680,2702,2740,2772,2776,2786,3150,3188,3192,3214,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1646 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1646 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1646 5 (fun x => (if x<2740 then (if x<1702 then (if x<1628 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<1642 then 1 else (if x<1692 then 1 else 2))) else (if x<1776 then (if x<1734 then 2 else (if x<1738 then 1 else 2)) else (if x<2680 then (if x<2638 then 0 else 1) else (if x<2702 then 0 else 2)))) else (if x<3192 then (if x<2786 then (if x<2772 then 0 else (if x<2776 then 1 else 2)) else (if x<3150 then 1 else (if x<3188 then 3 else 0))) else (if x<3256 then (if x<3214 then 3 else (if x<3252 then 4 else 4)) else (if x<3288 then (if x<3284 then 0 else 3) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1647 : Finset ℕ := ([18,48,72,132,222,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1647 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1647 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1647 18 5
  · have he : independentCachedBranchMembers1647.erase 18=independentCachedBranchMembers1645 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1645
  · have he : independentCachedBranchMembers1647.filter (independentCachedEdge 18)=independentCachedBranchMembers1646 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1646
def independentCachedBranchMembers1648 : Finset ℕ := ([1596,1628,1642,1650,1702,1734,1768,1776,2614,2638,2680,2714,2732,2740,2764,2772,2786,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1648 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1648 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1648 5 (fun x => (if x<2732 then (if x<1768 then (if x<1650 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<1702 then 1 else (if x<1734 then 0 else 1))) else (if x<2638 then (if x<1776 then 1 else (if x<2614 then 0 else 2)) else (if x<2680 then 2 else (if x<2714 then 0 else 2)))) else (if x<3162 then (if x<2772 then (if x<2740 then 2 else (if x<2764 then 0 else 1)) else (if x<2786 then 2 else (if x<3130 then 0 else 3))) else (if x<3214 then (if x<3180 then 4 else (if x<3188 then 3 else 4)) else (if x<3256 then (if x<3222 then 3 else 4) else (if x<3288 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1649 : Finset ℕ := ([1642,1650,1702,1734,2614,2638,2714,2786,3130,3162,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound1649 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1649 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1649 4 (fun x => (if x<2714 then (if x<1734 then (if x<1650 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 2 else 2))) else (if x<3162 then (if x<2786 then 2 else (if x<3130 then 0 else 1)) else (if x<3214 then 3 else (if x<3222 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1650 : Finset ℕ := ([252,1596,1628,1642,1650,1702,1734,1768,1776,2614,2638,2680,2714,2732,2740,2764,2772,2786,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1650 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1650 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1650 252 4
  · have he : independentCachedBranchMembers1650.erase 252=independentCachedBranchMembers1648 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1648
  · have he : independentCachedBranchMembers1650.filter (independentCachedEdge 252)=independentCachedBranchMembers1649 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1649
def independentCachedBranchMembers1651 : Finset ℕ := ([1596,1628,1768,1776,2614,2638,2714,2786,3180,3188,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1651 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1651 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1651 4 (fun x => (if x<2714 then (if x<1776 then (if x<1628 then 0 else (if x<1768 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 0 else 1))) else (if x<3188 then (if x<2786 then 2 else (if x<3180 then 0 else 2)) else (if x<3256 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1652 : Finset ℕ := ([132,252,1596,1628,1642,1650,1702,1734,1768,1776,2614,2638,2680,2714,2732,2740,2764,2772,2786,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1652 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1652 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1652 132 4
  · have he : independentCachedBranchMembers1652.erase 132=independentCachedBranchMembers1650 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1650
  · have he : independentCachedBranchMembers1652.filter (independentCachedEdge 132)=independentCachedBranchMembers1651 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1651
def independentCachedBranchMembers1653 : Finset ℕ := ([1596,1650,1734,1776,2714,2732,2772,2786,3130,3188,3214,3256] : List ℕ).toFinset
theorem independentCachedBranchBound1653 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1653 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1653 4 (fun x => (if x<2772 then (if x<1776 then (if x<1650 then 0 else (if x<1734 then 0 else 1)) else (if x<2714 then 1 else (if x<2732 then 2 else 0))) else (if x<3188 then (if x<2786 then 1 else (if x<3130 then 0 else 2)) else (if x<3214 then 2 else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1654 : Finset ℕ := ([72,132,252,1596,1628,1642,1650,1702,1734,1768,1776,2614,2638,2680,2714,2732,2740,2764,2772,2786,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1654 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1654 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1654 72 4
  · have he : independentCachedBranchMembers1654.erase 72=independentCachedBranchMembers1652 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1652
  · have he : independentCachedBranchMembers1654.filter (independentCachedEdge 72)=independentCachedBranchMembers1653 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1653
def independentCachedBranchMembers1655 : Finset ℕ := ([1628,1642,1702,1768,2714,2732,2772,2786,3162,3180,3222,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1655 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1655 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1655 4 (fun x => (if x<2772 then (if x<1768 then (if x<1642 then 0 else (if x<1702 then 0 else 1)) else (if x<2714 then 1 else (if x<2732 then 2 else 1))) else (if x<3180 then (if x<2786 then 0 else (if x<3162 then 0 else 2)) else (if x<3222 then 2 else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1656 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1702,1734,1768,1776,2614,2638,2680,2714,2732,2740,2764,2772,2786,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1656 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1656 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1656 48 4
  · have he : independentCachedBranchMembers1656.erase 48=independentCachedBranchMembers1654 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1654
  · have he : independentCachedBranchMembers1656.filter (independentCachedEdge 48)=independentCachedBranchMembers1655 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1655
def independentCachedBranchMembers1657 : Finset ℕ := ([48,72,132,252,1596,1642,1702,1776,2614,2638,2732,2772,3130,3180,3214,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1657 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1657 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1657 4 (fun x => (if x<2614 then (if x<1596 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1642 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2732 then (if x<2638 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3214 then (if x<3180 then 3 else 3) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1658 : Finset ℕ := ([48,72,132,252,1596,1628,1642,1650,1702,1734,1768,1776,2614,2638,2646,2680,2714,2732,2740,2764,2772,2786,3130,3162,3180,3188,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1658 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1658 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1658 2646 4
  · have he : independentCachedBranchMembers1658.erase 2646=independentCachedBranchMembers1656 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1656
  · have he : independentCachedBranchMembers1658.filter (independentCachedEdge 2646)=independentCachedBranchMembers1657 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1657
def independentCachedBranchMembers1659 : Finset ℕ := ([18,48,72,132,222,252,1596,1628,1642,1650,1692,1702,1714,1734,1738,1746,1764,1768,1776,2614,2618,2638,2646,2650,2668,2680,2702,2710,2714,2732,2740,2764,2772,2776,2786,3126,3130,3150,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1659 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1659 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1659 3226 5
  · have he : independentCachedBranchMembers1659.erase 3226=independentCachedBranchMembers1647 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1647
  · have he : independentCachedBranchMembers1659.filter (independentCachedEdge 3226)=independentCachedBranchMembers1658 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1658
def independentCachedBranchMembers1660 : Finset ℕ := ([132,252,1596,1642,1692,1702,1714,1738,1764,1776,2618,2646,2668,2680,2702,2740,2764,2776,2786,3126,3150,3162,3188,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1660 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1660 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1660 5 (fun x => (if x<2680 then (if x<1714 then (if x<1642 then (if x<252 then 0 else (if x<1596 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 0 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1764 then 2 else 0)) else (if x<2646 then (if x<2618 then 1 else 3) else (if x<2668 then 3 else 3)))) else (if x<3150 then (if x<2764 then (if x<2702 then 1 else (if x<2740 then 3 else 0)) else (if x<2786 then (if x<2776 then 0 else 3) else (if x<3126 then 1 else 2))) else (if x<3222 then (if x<3162 then 2 else (if x<3188 then 4 else 4)) else (if x<3256 then (if x<3244 then 4 else 0) else (if x<3284 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1661 : Finset ℕ := ([1596,1692,1764,1776,2618,2646,2702,2786,3188,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1661 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1661 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1661 4 (fun x => (if x<2702 then (if x<1776 then (if x<1692 then 0 else (if x<1764 then 1 else 0)) else (if x<2618 then 1 else (if x<2646 then 0 else 2))) else (if x<3244 then (if x<2786 then 1 else (if x<3188 then 0 else 2)) else (if x<3256 then 2 else (if x<3284 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1662 : Finset ℕ := ([72,132,252,1596,1642,1692,1702,1714,1738,1764,1776,2618,2646,2668,2680,2702,2740,2764,2776,2786,3126,3150,3162,3188,3222,3244,3256,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1662 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1662 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1662 72 4
  · have he : independentCachedBranchMembers1662.erase 72=independentCachedBranchMembers1660 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1660
  · have he : independentCachedBranchMembers1662.filter (independentCachedEdge 72)=independentCachedBranchMembers1661 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1661
def independentCachedBranchMembers1663 : Finset ℕ := ([1642,1692,1702,1764,2646,2668,2776,2786,3162,3222,3244,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1663 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1663 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1663 4 (fun x => (if x<2776 then (if x<1764 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<2646 then 1 else (if x<2668 then 2 else 2))) else (if x<3222 then (if x<2786 then 2 else (if x<3162 then 0 else 3)) else (if x<3244 then 3 else (if x<3284 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
