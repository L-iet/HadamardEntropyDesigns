/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch211
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9568 : Finset ℕ := ([36,48,1590,1596,1708,1714,2614,2618,2732,2740,3118,3132,3238,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9568 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9568 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9568 5 (fun x => (if x<2618 then (if x<1596 then (if x<48 then 0 else (if x<1590 then 1 else 0)) else (if x<1714 then (if x<1708 then 1 else 0) else (if x<2614 then 1 else 1))) else (if x<3132 then (if x<2740 then (if x<2732 then 2 else 2) else (if x<3118 then 0 else 2)) else (if x<3252 then (if x<3238 then 0 else 0) else (if x<3256 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9569 : Finset ℕ := ([36,48,66,72,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2740,2758,2762,2776,3118,3132,3158,3162,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9569 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9569 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9569 222 5
  · have he : independentCachedBranchMembers9569.erase 222=independentCachedBranchMembers9567 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9567
  · have he : independentCachedBranchMembers9569.filter (independentCachedEdge 222)=independentCachedBranchMembers9568 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9568
def independentCachedBranchMembers9570 : Finset ℕ := ([66,72,1614,1626,1708,1714,2638,2652,2732,2740,3158,3162,3238,3252,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9570 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9570 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9570 5 (fun x => (if x<2652 then (if x<1626 then (if x<72 then 0 else (if x<1614 then 1 else 0)) else (if x<1714 then (if x<1708 then 1 else 0) else (if x<2638 then 1 else 1))) else (if x<3162 then (if x<2740 then (if x<2732 then 2 else 2) else (if x<3158 then 0 else 2)) else (if x<3252 then (if x<3238 then 0 else 2) else (if x<3256 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9571 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2740,2758,2762,2776,3118,3132,3158,3162,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9571 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9571 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9571 192 5
  · have he : independentCachedBranchMembers9571.erase 192=independentCachedBranchMembers9569 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9569
  · have he : independentCachedBranchMembers9571.filter (independentCachedEdge 192)=independentCachedBranchMembers9570 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9570
def independentCachedBranchMembers9572 : Finset ℕ := ([36,48,66,192,1590,1708,1734,1738,2614,2618,2652,2732,2740,2758,2762,3132,3158,3162,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9572 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9572 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9572 5 (fun x => (if x<2652 then (if x<1708 then (if x<66 then (if x<48 then 0 else 1) else (if x<192 then 0 else (if x<1590 then 1 else 1))) else (if x<1738 then (if x<1734 then 0 else 1) else (if x<2614 then 0 else (if x<2618 then 2 else 1)))) else (if x<3132 then (if x<2740 then (if x<2732 then 2 else 2) else (if x<2758 then 0 else (if x<2762 then 2 else 1))) else (if x<3162 then (if x<3158 then 0 else 2) else (if x<3238 then 0 else (if x<3276 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9573 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2740,2758,2762,2776,3118,3132,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9573 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9573 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9573 3164 5
  · have he : independentCachedBranchMembers9573.erase 3164=independentCachedBranchMembers9571 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9571
  · have he : independentCachedBranchMembers9573.filter (independentCachedEdge 3164)=independentCachedBranchMembers9572 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9572
def independentCachedBranchMembers9574 : Finset ℕ := ([36,66,72,222,1614,1708,1738,1752,2618,2638,2652,2732,2740,2762,2776,3118,3132,3162,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9574 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9574 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9574 5 (fun x => (if x<2652 then (if x<1708 then (if x<72 then (if x<66 then 0 else 0) else (if x<222 then 1 else (if x<1614 then 1 else 1))) else (if x<1752 then (if x<1738 then 0 else 0) else (if x<2618 then 1 else (if x<2638 then 2 else 2)))) else (if x<3118 then (if x<2740 then (if x<2732 then 1 else 2) else (if x<2762 then 0 else (if x<2776 then 1 else 2))) else (if x<3162 then (if x<3132 then 2 else 0) else (if x<3256 then 0 else (if x<3276 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9575 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2732,2740,2758,2762,2776,3118,3130,3132,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9575 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9575 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9575 3130 5
  · have he : independentCachedBranchMembers9575.erase 3130=independentCachedBranchMembers9573 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9573
  · have he : independentCachedBranchMembers9575.filter (independentCachedEdge 3130)=independentCachedBranchMembers9574 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9574
def independentCachedBranchMembers9576 : Finset ℕ := ([48,192,1590,1596,1626,1714,1734,1748,2618,2638,2652,2732,2740,2762,2776,3118,3132,3162,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9576 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9576 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9576 5 (fun x => (if x<2652 then (if x<1714 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1596 then 0 else (if x<1626 then 1 else 1))) else (if x<1748 then (if x<1734 then 1 else 0) else (if x<2618 then 1 else (if x<2638 then 0 else 2)))) else (if x<3118 then (if x<2740 then (if x<2732 then 1 else 2) else (if x<2762 then 1 else (if x<2776 then 0 else 2))) else (if x<3162 then (if x<3132 then 2 else 0) else (if x<3256 then 2 else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9577 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2650,2652,2732,2740,2758,2762,2776,3118,3130,3132,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9577 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9577 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9577 2650 5
  · have he : independentCachedBranchMembers9577.erase 2650=independentCachedBranchMembers9575 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9575
  · have he : independentCachedBranchMembers9577.filter (independentCachedEdge 2650)=independentCachedBranchMembers9576 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9576
def independentCachedBranchMembers9578 : Finset ℕ := ([72,222,1596,1614,1626,1714,1748,1752,2614,2618,2652,2732,2740,2758,2762,3132,3158,3162,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9578 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9578 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9578 5 (fun x => (if x<2652 then (if x<1714 then (if x<1596 then (if x<222 then 0 else 0) else (if x<1614 then 1 else (if x<1626 then 0 else 1))) else (if x<1752 then (if x<1748 then 1 else 1) else (if x<2614 then 0 else (if x<2618 then 2 else 1)))) else (if x<3132 then (if x<2740 then (if x<2732 then 0 else 2) else (if x<2758 then 1 else (if x<2762 then 2 else 0))) else (if x<3162 then (if x<3158 then 2 else 2) else (if x<3238 then 0 else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9579 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2620,2638,2650,2652,2732,2740,2758,2762,2776,3118,3130,3132,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9579 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9579 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9579 2620 5
  · have he : independentCachedBranchMembers9579.erase 2620=independentCachedBranchMembers9577 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9577
  · have he : independentCachedBranchMembers9579.filter (independentCachedEdge 2620)=independentCachedBranchMembers9578 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9578
def independentCachedBranchMembers9580 : Finset ℕ := ([36,192,1590,1596,1614,1708,1748,1752,2614,2618,2620,2638,2732,2776,3118,3158,3162,3164,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9580 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9580 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9580 5 (fun x => (if x<2638 then (if x<1708 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1596 then 0 else (if x<1614 then 1 else 1))) else (if x<2614 then (if x<1748 then 2 else (if x<1752 then 1 else 2)) else (if x<2618 then 3 else (if x<2620 then 4 else 0)))) else (if x<3162 then (if x<2776 then (if x<2732 then 3 else 3) else (if x<3118 then 0 else (if x<3158 then 0 else 3))) else (if x<3256 then (if x<3164 then 2 else (if x<3252 then 1 else 1)) else (if x<3274 then 2 else (if x<3276 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9581 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2620,2638,2650,2652,2732,2740,2758,2762,2776,3118,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9581 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9581 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9581 3150 5
  · have he : independentCachedBranchMembers9581.erase 3150=independentCachedBranchMembers9579 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9579
  · have he : independentCachedBranchMembers9581.filter (independentCachedEdge 3150)=independentCachedBranchMembers9580 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9580
def independentCachedBranchMembers9582 : Finset ℕ := ([66,222,1590,1614,1626,1708,1734,1748,2614,2638,2650,2652,2732,2758,3118,3130,3132,3158,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9582 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9582 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9582 5 (fun x => (if x<2652 then (if x<1708 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1614 then 1 else (if x<1626 then 0 else 1))) else (if x<2614 then (if x<1734 then 2 else (if x<1748 then 1 else 2)) else (if x<2638 then 3 else (if x<2650 then 3 else 0)))) else (if x<3132 then (if x<2758 then (if x<2732 then 4 else 3) else (if x<3118 then 0 else (if x<3130 then 2 else 1))) else (if x<3252 then (if x<3158 then 4 else (if x<3238 then 0 else 1)) else (if x<3274 then 2 else (if x<3276 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9583 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2620,2638,2650,2652,2732,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9583 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9583 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9583 3126 5
  · have he : independentCachedBranchMembers9583.erase 3126=independentCachedBranchMembers9581 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9581
  · have he : independentCachedBranchMembers9583.filter (independentCachedEdge 3126)=independentCachedBranchMembers9582 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9582
def independentCachedBranchMembers9584 : Finset ℕ := ([36,66,192,222,1596,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2740,3118,3132,3158,3162,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9584 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9584 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9584 5 (fun x => (if x<1752 then (if x<1626 then (if x<192 then (if x<66 then 0 else 0) else (if x<222 then 1 else (if x<1596 then 1 else 0))) else (if x<1734 then (if x<1708 then 0 else (if x<1714 then 2 else 2)) else (if x<1738 then 1 else (if x<1748 then 2 else 2)))) else (if x<2740 then (if x<2618 then (if x<2614 then 1 else 3) else (if x<2638 then 4 else (if x<2652 then 3 else 4))) else (if x<3158 then (if x<3118 then 0 else (if x<3132 then 3 else 4)) else (if x<3162 then 3 else (if x<3274 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9585 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2620,2638,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9585 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9585 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9585 2738 5
  · have he : independentCachedBranchMembers9585.erase 2738=independentCachedBranchMembers9583 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9583
  · have he : independentCachedBranchMembers9585.filter (independentCachedEdge 2738)=independentCachedBranchMembers9584 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9584
def independentCachedBranchMembers9586 : Finset ℕ := ([36,48,72,192,1596,1714,1738,1752,2614,2638,2650,2652,2732,2758,3118,3130,3132,3158,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9586 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9586 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9586 5 (fun x => (if x<2652 then (if x<1714 then (if x<72 then (if x<48 then 0 else 1) else (if x<192 then 0 else (if x<1596 then 1 else 1))) else (if x<2614 then (if x<1738 then 2 else (if x<1752 then 0 else 2)) else (if x<2638 then 0 else (if x<2650 then 3 else 0)))) else (if x<3132 then (if x<2758 then (if x<2732 then 2 else 3) else (if x<3118 then 1 else (if x<3130 then 3 else 1))) else (if x<3252 then (if x<3158 then 4 else (if x<3238 then 3 else 2)) else (if x<3274 then 0 else (if x<3276 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9587 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9587 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9587 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9587 2646 5
  · have he : independentCachedBranchMembers9587.erase 2646=independentCachedBranchMembers9585 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9585
  · have he : independentCachedBranchMembers9587.filter (independentCachedEdge 2646)=independentCachedBranchMembers9586 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9586
def independentCachedBranchMembers9588 : Finset ℕ := ([48,66,72,222,1626,1714,1734,1738,2614,2618,2620,2638,2732,2776,3118,3158,3162,3164,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9588 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9588 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9588 5 (fun x => (if x<2638 then (if x<1714 then (if x<72 then (if x<66 then 0 else 0) else (if x<222 then 1 else (if x<1626 then 1 else 1))) else (if x<2614 then (if x<1734 then 2 else (if x<1738 then 0 else 2)) else (if x<2618 then 2 else (if x<2620 then 3 else 0)))) else (if x<3162 then (if x<2776 then (if x<2732 then 0 else 3) else (if x<3118 then 1 else (if x<3158 then 3 else 4))) else (if x<3256 then (if x<3164 then 3 else (if x<3252 then 1 else 2)) else (if x<3274 then 0 else (if x<3276 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9589 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9589 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9589 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9589 2606 5
  · have he : independentCachedBranchMembers9589.erase 2606=independentCachedBranchMembers9587 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9587
  · have he : independentCachedBranchMembers9589.filter (independentCachedEdge 2606)=independentCachedBranchMembers9588 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9588
def independentCachedBranchMembers9590 : Finset ℕ := ([48,72,1596,1626,1708,1714,1734,1738,1748,1752,2614,2618,2638,2652,2740,3126,3130,3150,3164,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9590 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9590 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9590 5 (fun x => (if x<2638 then (if x<1734 then (if x<1626 then (if x<72 then 0 else (if x<1596 then 0 else 1)) else (if x<1708 then 1 else (if x<1714 then 2 else 0))) else (if x<1752 then (if x<1738 then 2 else (if x<1748 then 0 else 1)) else (if x<2614 then 2 else (if x<2618 then 0 else 1)))) else (if x<3164 then (if x<3126 then (if x<2652 then 0 else (if x<2740 then 1 else 1)) else (if x<3130 then 3 else (if x<3150 then 4 else 3))) else (if x<3256 then (if x<3238 then 4 else (if x<3252 then 2 else 0)) else (if x<3276 then 2 else (if x<3282 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9591 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9591 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9591 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9591 1746 5
  · have he : independentCachedBranchMembers9591.erase 1746=independentCachedBranchMembers9589 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9589
  · have he : independentCachedBranchMembers9591.filter (independentCachedEdge 1746)=independentCachedBranchMembers9590 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9590
def independentCachedBranchMembers9592 : Finset ℕ := ([36,66,1590,1614,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2740,3118,3132,3158,3162,3238,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9592 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9592 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9592 5 (fun x => (if x<2646 then (if x<1734 then (if x<1614 then (if x<66 then 0 else (if x<1590 then 0 else 1)) else (if x<1708 then 1 else (if x<1714 then 0 else 2))) else (if x<1752 then (if x<1738 then 2 else (if x<1748 then 0 else 1)) else (if x<2606 then 2 else (if x<2620 then 1 else 0)))) else (if x<3162 then (if x<3118 then (if x<2650 then 1 else (if x<2740 then 0 else 1)) else (if x<3132 then 3 else (if x<3158 then 4 else 3))) else (if x<3256 then (if x<3238 then 4 else (if x<3252 then 2 else 0)) else (if x<3276 then 2 else (if x<3282 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9593 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9593 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9593 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9593 1740 5
  · have he : independentCachedBranchMembers9593.erase 1740=independentCachedBranchMembers9591 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9591
  · have he : independentCachedBranchMembers9593.filter (independentCachedEdge 1740)=independentCachedBranchMembers9592 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9592
def independentCachedBranchMembers9594 : Finset ℕ := ([192,222,1590,1596,1614,1626,1708,1714,1738,1748,2606,2618,2646,2652,2740,2758,2776,3118,3130,3158,3164,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9594 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9594 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9594 5 (fun x => (if x<2646 then (if x<1708 then (if x<1596 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1614 then 2 else (if x<1626 then 1 else 2))) else (if x<1748 then (if x<1714 then 1 else (if x<1738 then 2 else 0)) else (if x<2606 then 0 else (if x<2618 then 1 else 2)))) else (if x<3130 then (if x<2758 then (if x<2652 then 1 else (if x<2740 then 2 else 1)) else (if x<2776 then 0 else (if x<3118 then 0 else 3))) else (if x<3252 then (if x<3158 then 4 else (if x<3164 then 3 else 4)) else (if x<3276 then 3 else (if x<3282 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9595 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1708,1714,1716,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9595 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9595 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9595 1716 5
  · have he : independentCachedBranchMembers9595.erase 1716=independentCachedBranchMembers9593 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9593
  · have he : independentCachedBranchMembers9595.filter (independentCachedEdge 1716)=independentCachedBranchMembers9594 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9594
def independentCachedBranchMembers9596 : Finset ℕ := ([36,48,66,72,192,222,1708,1714,1738,1748,2614,2620,2638,2650,2740,2758,2776,3126,3132,3150,3162,3252,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9596 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9596 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9596 5 (fun x => (if x<2638 then (if x<1708 then (if x<72 then (if x<48 then 0 else (if x<66 then 1 else 0)) else (if x<192 then 1 else (if x<222 then 2 else 2))) else (if x<1748 then (if x<1714 then 0 else (if x<1738 then 1 else 0)) else (if x<2614 then 2 else (if x<2620 then 1 else 0)))) else (if x<3132 then (if x<2758 then (if x<2650 then 1 else (if x<2740 then 0 else 3)) else (if x<2776 then 2 else (if x<3126 then 2 else 3))) else (if x<3252 then (if x<3150 then 4 else (if x<3162 then 3 else 4)) else (if x<3276 then 0 else (if x<3282 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9597 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1706,1708,1714,1716,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9597 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9597 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9597 1706 5
  · have he : independentCachedBranchMembers9597.erase 1706=independentCachedBranchMembers9595 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9595
  · have he : independentCachedBranchMembers9597.filter (independentCachedEdge 1706)=independentCachedBranchMembers9596 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9596
def independentCachedBranchMembers9598 : Finset ℕ := ([36,72,1596,1614,1706,1708,1714,1716,1734,1752,2606,2614,2650,2652,2762,3118,3126,3162,3164,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9598 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9598 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9598 5 (fun x => (if x<2650 then (if x<1714 then (if x<1614 then (if x<72 then 0 else (if x<1596 then 0 else 1)) else (if x<1706 then 1 else (if x<1708 then 1 else 2))) else (if x<1752 then (if x<1716 then 2 else (if x<1734 then 0 else 2)) else (if x<2606 then 0 else (if x<2614 then 1 else 0)))) else (if x<3164 then (if x<3118 then (if x<2652 then 0 else (if x<2762 then 1 else 1)) else (if x<3126 then 3 else (if x<3162 then 4 else 3))) else (if x<3274 then (if x<3238 then 4 else (if x<3256 then 0 else 2)) else (if x<3276 then 0 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9599 : Finset ℕ := ([36,1596,1706,1708,1714,1716,2606,2614,3118,3126,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9599 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9599 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9599 4 (fun x => (if x<2606 then (if x<1708 then (if x<1596 then 0 else (if x<1706 then 0 else 1)) else (if x<1714 then 2 else (if x<1716 then 2 else 1))) else (if x<3126 then (if x<2614 then 0 else (if x<3118 then 3 else 3)) else (if x<3238 then 0 else (if x<3256 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
