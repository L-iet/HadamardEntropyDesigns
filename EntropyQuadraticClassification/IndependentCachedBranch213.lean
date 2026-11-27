/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch212
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9600 : Finset ℕ := ([36,72,222,1596,1614,1706,1708,1714,1716,1734,1752,2606,2614,2650,2652,2762,3118,3126,3162,3164,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9600 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9600 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9600 222 4
  · have he : independentCachedBranchMembers9600.erase 222=independentCachedBranchMembers9598 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9598
  · have he : independentCachedBranchMembers9600.filter (independentCachedEdge 222)=independentCachedBranchMembers9599 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9599
def independentCachedBranchMembers9601 : Finset ℕ := ([72,1614,1706,1708,1714,1716,2650,2652,3162,3164,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9601 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9601 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9601 4 (fun x => (if x<2650 then (if x<1708 then (if x<1614 then 0 else (if x<1706 then 0 else 1)) else (if x<1714 then 2 else (if x<1716 then 2 else 1))) else (if x<3164 then (if x<2652 then 0 else (if x<3162 then 3 else 3)) else (if x<3238 then 0 else (if x<3256 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9602 : Finset ℕ := ([36,72,192,222,1596,1614,1706,1708,1714,1716,1734,1752,2606,2614,2650,2652,2762,3118,3126,3162,3164,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9602 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9602 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9602 192 4
  · have he : independentCachedBranchMembers9602.erase 192=independentCachedBranchMembers9600 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9600
  · have he : independentCachedBranchMembers9602.filter (independentCachedEdge 192)=independentCachedBranchMembers9601 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9601
def independentCachedBranchMembers9603 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9603 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9603 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9603 1720 5
  · have he : independentCachedBranchMembers9603.erase 1720=independentCachedBranchMembers9597 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9597
  · have he : independentCachedBranchMembers9603.filter (independentCachedEdge 1720)=independentCachedBranchMembers9602 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9602
def independentCachedBranchMembers9604 : Finset ℕ := ([48,66,1590,1626,1706,1708,1714,1716,1734,1752,2618,2620,2638,2646,2762,3130,3132,3150,3158,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9604 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9604 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9604 5 (fun x => (if x<2638 then (if x<1714 then (if x<1626 then (if x<66 then 0 else (if x<1590 then 0 else 1)) else (if x<1706 then 1 else (if x<1708 then 1 else 2))) else (if x<1752 then (if x<1716 then 2 else (if x<1734 then 0 else 0)) else (if x<2618 then 2 else (if x<2620 then 1 else 0)))) else (if x<3158 then (if x<3130 then (if x<2646 then 0 else (if x<2762 then 1 else 1)) else (if x<3132 then 3 else (if x<3150 then 4 else 3))) else (if x<3274 then (if x<3238 then 4 else (if x<3256 then 2 else 0)) else (if x<3276 then 0 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9605 : Finset ℕ := ([48,1590,1706,1708,1714,1716,2618,2620,3130,3132,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9605 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9605 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9605 4 (fun x => (if x<2618 then (if x<1708 then (if x<1590 then 0 else (if x<1706 then 0 else 1)) else (if x<1714 then 2 else (if x<1716 then 2 else 1))) else (if x<3132 then (if x<2620 then 0 else (if x<3130 then 3 else 3)) else (if x<3238 then 0 else (if x<3256 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9606 : Finset ℕ := ([48,66,222,1590,1626,1706,1708,1714,1716,1734,1752,2618,2620,2638,2646,2762,3130,3132,3150,3158,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9606 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9606 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9606 222 4
  · have he : independentCachedBranchMembers9606.erase 222=independentCachedBranchMembers9604 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9604
  · have he : independentCachedBranchMembers9606.filter (independentCachedEdge 222)=independentCachedBranchMembers9605 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9605
def independentCachedBranchMembers9607 : Finset ℕ := ([66,1626,1706,1708,1714,1716,2638,2646,3150,3158,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9607 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9607 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9607 4 (fun x => (if x<2638 then (if x<1708 then (if x<1626 then 0 else (if x<1706 then 0 else 1)) else (if x<1714 then 2 else (if x<1716 then 2 else 1))) else (if x<3158 then (if x<2646 then 0 else (if x<3150 then 3 else 3)) else (if x<3238 then 0 else (if x<3256 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9608 : Finset ℕ := ([48,66,192,222,1590,1626,1706,1708,1714,1716,1734,1752,2618,2620,2638,2646,2762,3130,3132,3150,3158,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9608 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9608 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9608 192 4
  · have he : independentCachedBranchMembers9608.erase 192=independentCachedBranchMembers9606 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9606
  · have he : independentCachedBranchMembers9608.filter (independentCachedEdge 192)=independentCachedBranchMembers9607 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9607
def independentCachedBranchMembers9609 : Finset ℕ := ([36,48,66,72,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9609 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9609 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9609 1702 5
  · have he : independentCachedBranchMembers9609.erase 1702=independentCachedBranchMembers9603 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9603
  · have he : independentCachedBranchMembers9609.filter (independentCachedEdge 1702)=independentCachedBranchMembers9608 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9608
def independentCachedBranchMembers9610 : Finset ℕ := ([66,72,222,1614,1626,1738,1740,1746,1748,2638,2646,2650,2652,2758,2762,2776,3150,3158,3162,3164,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9610 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9610 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9610 5 (fun x => (if x<2650 then (if x<1738 then (if x<222 then (if x<72 then 0 else 1) else (if x<1614 then 0 else (if x<1626 then 0 else 1))) else (if x<1748 then (if x<1740 then 2 else (if x<1746 then 1 else 0)) else (if x<2638 then 2 else (if x<2646 then 1 else 0)))) else (if x<3158 then (if x<2762 then (if x<2652 then 3 else (if x<2758 then 4 else 2)) else (if x<2776 then 0 else (if x<3150 then 1 else 3))) else (if x<3274 then (if x<3162 then 4 else (if x<3164 then 0 else 1)) else (if x<3276 then 1 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9611 : Finset ℕ := ([66,1626,1738,1740,1746,1748,2638,2646,2758,2776,3150,3158] : List ℕ).toFinset
theorem independentCachedBranchBound9611 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9611 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9611 4 (fun x => (if x<2638 then (if x<1740 then (if x<1626 then 0 else (if x<1738 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2776 then (if x<2646 then 0 else (if x<2758 then 3 else 1)) else (if x<3150 then 1 else (if x<3158 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9612 : Finset ℕ := ([66,72,222,1614,1626,1738,1740,1746,1748,1752,2638,2646,2650,2652,2758,2762,2776,3150,3158,3162,3164,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9612 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9612 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9612 1752 4
  · have he : independentCachedBranchMembers9612.erase 1752=independentCachedBranchMembers9610 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9610
  · have he : independentCachedBranchMembers9612.filter (independentCachedEdge 1752)=independentCachedBranchMembers9611 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9611
def independentCachedBranchMembers9613 : Finset ℕ := ([72,1614,1738,1740,1746,1748,2650,2652,2758,2776,3162,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9613 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9613 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9613 4 (fun x => (if x<2650 then (if x<1740 then (if x<1614 then 0 else (if x<1738 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2776 then (if x<2652 then 0 else (if x<2758 then 3 else 1)) else (if x<3162 then 1 else (if x<3164 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9614 : Finset ℕ := ([66,72,222,1614,1626,1734,1738,1740,1746,1748,1752,2638,2646,2650,2652,2758,2762,2776,3150,3158,3162,3164,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9614 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9614 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9614 1734 4
  · have he : independentCachedBranchMembers9614.erase 1734=independentCachedBranchMembers9612 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9612
  · have he : independentCachedBranchMembers9614.filter (independentCachedEdge 1734)=independentCachedBranchMembers9613 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9613
def independentCachedBranchMembers9615 : Finset ℕ := ([66,72,1614,1626,2638,2646,2650,2652,3150,3158,3162,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9615 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9615 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9615 4 (fun x => (if x<2650 then (if x<1626 then (if x<72 then 0 else (if x<1614 then 1 else 0)) else (if x<2638 then 1 else (if x<2646 then 1 else 0))) else (if x<3158 then (if x<2652 then 2 else (if x<3150 then 3 else 2)) else (if x<3162 then 3 else (if x<3164 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9616 : Finset ℕ := ([66,72,192,222,1614,1626,1734,1738,1740,1746,1748,1752,2638,2646,2650,2652,2758,2762,2776,3150,3158,3162,3164,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9616 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9616 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9616 192 4
  · have he : independentCachedBranchMembers9616.erase 192=independentCachedBranchMembers9614 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9614
  · have he : independentCachedBranchMembers9616.filter (independentCachedEdge 192)=independentCachedBranchMembers9615 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9615
def independentCachedBranchMembers9617 : Finset ℕ := ([36,48,66,72,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9617 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9617 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9617 190 5
  · have he : independentCachedBranchMembers9617.erase 190=independentCachedBranchMembers9609 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9609
  · have he : independentCachedBranchMembers9617.filter (independentCachedEdge 190)=independentCachedBranchMembers9616 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9616
def independentCachedBranchMembers9618 : Finset ℕ := ([36,48,192,1590,1596,1738,1740,1746,1748,2606,2614,2618,2620,2758,2762,2776,3118,3126,3130,3132,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9618 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9618 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9618 5 (fun x => (if x<2618 then (if x<1738 then (if x<192 then (if x<48 then 0 else 1) else (if x<1590 then 0 else (if x<1596 then 0 else 1))) else (if x<1748 then (if x<1740 then 2 else (if x<1746 then 1 else 0)) else (if x<2606 then 2 else (if x<2614 then 0 else 1)))) else (if x<3126 then (if x<2762 then (if x<2620 then 3 else (if x<2758 then 4 else 1)) else (if x<2776 then 0 else (if x<3118 then 2 else 3))) else (if x<3274 then (if x<3130 then 4 else (if x<3132 then 1 else 0)) else (if x<3276 then 1 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9619 : Finset ℕ := ([48,1590,1738,1740,1746,1748,2618,2620,2758,2776,3130,3132] : List ℕ).toFinset
theorem independentCachedBranchBound9619 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9619 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9619 4 (fun x => (if x<2618 then (if x<1740 then (if x<1590 then 0 else (if x<1738 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2776 then (if x<2620 then 0 else (if x<2758 then 3 else 1)) else (if x<3130 then 1 else (if x<3132 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9620 : Finset ℕ := ([36,48,192,1590,1596,1738,1740,1746,1748,1752,2606,2614,2618,2620,2758,2762,2776,3118,3126,3130,3132,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9620 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9620 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9620 1752 4
  · have he : independentCachedBranchMembers9620.erase 1752=independentCachedBranchMembers9618 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9618
  · have he : independentCachedBranchMembers9620.filter (independentCachedEdge 1752)=independentCachedBranchMembers9619 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9619
def independentCachedBranchMembers9621 : Finset ℕ := ([36,1596,1738,1740,1746,1748,2606,2614,2758,2776,3118,3126] : List ℕ).toFinset
theorem independentCachedBranchBound9621 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9621 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9621 4 (fun x => (if x<2606 then (if x<1740 then (if x<1596 then 0 else (if x<1738 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 2 else 1))) else (if x<2776 then (if x<2614 then 0 else (if x<2758 then 3 else 1)) else (if x<3118 then 1 else (if x<3126 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9622 : Finset ℕ := ([36,48,192,1590,1596,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2758,2762,2776,3118,3126,3130,3132,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9622 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9622 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9622 1734 4
  · have he : independentCachedBranchMembers9622.erase 1734=independentCachedBranchMembers9620 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9620
  · have he : independentCachedBranchMembers9622.filter (independentCachedEdge 1734)=independentCachedBranchMembers9621 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9621
def independentCachedBranchMembers9623 : Finset ℕ := ([36,48,1590,1596,2606,2614,2618,2620,3118,3126,3130,3132] : List ℕ).toFinset
theorem independentCachedBranchBound9623 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9623 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9623 4 (fun x => (if x<2618 then (if x<1596 then (if x<48 then 0 else (if x<1590 then 1 else 0)) else (if x<2606 then 1 else (if x<2614 then 0 else 1))) else (if x<3126 then (if x<2620 then 2 else (if x<3118 then 3 else 2)) else (if x<3130 then 3 else (if x<3132 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9624 : Finset ℕ := ([36,48,192,222,1590,1596,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2758,2762,2776,3118,3126,3130,3132,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9624 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9624 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9624 222 4
  · have he : independentCachedBranchMembers9624.erase 222=independentCachedBranchMembers9622 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9622
  · have he : independentCachedBranchMembers9624.filter (independentCachedEdge 222)=independentCachedBranchMembers9623 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9623
def independentCachedBranchMembers9625 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9625 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9625 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9625 160 5
  · have he : independentCachedBranchMembers9625.erase 160=independentCachedBranchMembers9617 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9617
  · have he : independentCachedBranchMembers9625.filter (independentCachedEdge 160)=independentCachedBranchMembers9624 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9624
def independentCachedBranchMembers9626 : Finset ℕ := ([48,66,160,190,1596,1614,1706,1708,1714,1716,1734,1752,2618,2620,2638,2646,2732,2738,2740,2758,2776,3118,3126,3162,3164,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9626 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9626 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9626 5 (fun x => (if x<2646 then (if x<1708 then (if x<190 then (if x<66 then 0 else (if x<160 then 0 else 1)) else (if x<1614 then (if x<1596 then 1 else 0) else (if x<1706 then 0 else 1))) else (if x<1752 then (if x<1716 then (if x<1714 then 2 else 2) else (if x<1734 then 1 else 2)) else (if x<2620 then (if x<2618 then 2 else 3) else (if x<2638 then 4 else 3)))) else (if x<3126 then (if x<2740 then (if x<2732 then 4 else (if x<2738 then 1 else 1)) else (if x<2776 then (if x<2758 then 0 else 0) else (if x<3118 then 3 else 3))) else (if x<3256 then (if x<3164 then (if x<3162 then 4 else 3) else (if x<3238 then 4 else 1)) else (if x<3276 then (if x<3274 then 0 else 0) else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9627 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9627 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9627 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9627 3288 5
  · have he : independentCachedBranchMembers9627.erase 3288=independentCachedBranchMembers9625 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9625
  · have he : independentCachedBranchMembers9627.filter (independentCachedEdge 3288)=independentCachedBranchMembers9626 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9626
def independentCachedBranchMembers9628 : Finset ℕ := ([36,72,160,190,1590,1626,1706,1708,1714,1716,1734,1752,2606,2614,2650,2652,2732,2738,2740,2758,2776,3130,3132,3150,3158,3238,3256,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9628 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9628 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9628 5 (fun x => (if x<2652 then (if x<1708 then (if x<190 then (if x<72 then 0 else (if x<160 then 0 else 1)) else (if x<1626 then (if x<1590 then 1 else 0) else (if x<1706 then 0 else 1))) else (if x<1752 then (if x<1716 then (if x<1714 then 2 else 2) else (if x<1734 then 1 else 2)) else (if x<2614 then (if x<2606 then 2 else 3) else (if x<2650 then 4 else 3)))) else (if x<3132 then (if x<2740 then (if x<2732 then 4 else (if x<2738 then 1 else 1)) else (if x<2776 then (if x<2758 then 0 else 3) else (if x<3130 then 0 else 3))) else (if x<3256 then (if x<3158 then (if x<3150 then 4 else 3) else (if x<3238 then 4 else 0)) else (if x<3276 then (if x<3274 then 1 else 0) else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9629 : Finset ℕ := ([36,48,66,72,160,190,192,222,1590,1596,1614,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2732,2738,2740,2758,2762,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9629 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9629 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9629 3270 5
  · have he : independentCachedBranchMembers9629.erase 3270=independentCachedBranchMembers9627 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9627
  · have he : independentCachedBranchMembers9629.filter (independentCachedEdge 3270)=independentCachedBranchMembers9628 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9628
def independentCachedBranchMembers9630 : Finset ℕ := ([72,192,222,1590,1614,1706,1716,1734,1740,1746,1752,2614,2620,2638,2650,2758,2776,3118,3130,3158,3164,3238,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9630 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9630 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9630 5 (fun x => (if x<2620 then (if x<1716 then (if x<1590 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1614 then 1 else (if x<1706 then 0 else 2))) else (if x<1746 then (if x<1734 then 2 else (if x<1740 then 1 else 2)) else (if x<1752 then 2 else (if x<2614 then 0 else 3)))) else (if x<3130 then (if x<2758 then (if x<2638 then 1 else (if x<2650 then 3 else 0)) else (if x<2776 then 4 else (if x<3118 then 4 else 3))) else (if x<3238 then (if x<3158 then 1 else (if x<3164 then 3 else 0)) else (if x<3256 then 4 else (if x<3274 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9631 : Finset ℕ := ([222,1706,1746,1752,2650,2776,3118,3158,3164,3238] : List ℕ).toFinset
theorem independentCachedBranchBound9631 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9631 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9631 4 (fun x => (if x<2776 then (if x<1746 then (if x<1706 then 0 else 1) else (if x<1752 then 0 else (if x<2650 then 1 else 0))) else (if x<3158 then (if x<3118 then 2 else 1) else (if x<3164 then 0 else (if x<3238 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
