/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch215
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9696 : Finset ℕ := ([66,72,160,222,1590,1596,1614,1702,1706,1708,1746,1748,1752,2606,2646,2650,2652,2738,2740,2758,2762,3118,3158,3162,3164,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9696 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9696 3270 4
  · have he : independentCachedBranchMembers9696.erase 3270=independentCachedBranchMembers9692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9692
  · have he : independentCachedBranchMembers9696.filter (independentCachedEdge 3270)=independentCachedBranchMembers9695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9695
def independentCachedBranchMembers9697 : Finset ℕ := ([72,222,1590,1702,1746,1748,2646,2738,2740,2758,3118,3162,3164,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9697 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9697 4 (fun x => (if x<2740 then (if x<1746 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1702 then 1 else 2)) else (if x<2646 then (if x<1748 then 1 else 2) else (if x<2738 then 1 else 1))) else (if x<3164 then (if x<3118 then (if x<2758 then 2 else 2) else (if x<3162 then 3 else 0)) else (if x<3274 then (if x<3256 then 3 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9698 : Finset ℕ := ([66,72,160,222,1590,1596,1614,1702,1706,1708,1746,1748,1752,2606,2646,2650,2652,2738,2740,2744,2758,2762,3118,3158,3162,3164,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9698 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9698 2744 4
  · have he : independentCachedBranchMembers9698.erase 2744=independentCachedBranchMembers9696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9696
  · have he : independentCachedBranchMembers9698.filter (independentCachedEdge 2744)=independentCachedBranchMembers9697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9697
def independentCachedBranchMembers9699 : Finset ℕ := ([160,222,1702,1706,1708,1746,1748,1752,2606,2646,2650,2652,3118,3158,3162,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9699 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9699 4 (fun x => (if x<2606 then (if x<1708 then (if x<1702 then (if x<222 then 0 else 1) else (if x<1706 then 0 else 2)) else (if x<1748 then (if x<1746 then 3 else 1) else (if x<1752 then 3 else 2))) else (if x<3118 then (if x<2650 then (if x<2646 then 2 else 1) else (if x<2652 then 0 else 2)) else (if x<3162 then (if x<3158 then 3 else 3) else (if x<3164 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9700 : Finset ℕ := ([48,66,72,160,222,1590,1596,1614,1702,1706,1708,1746,1748,1752,2606,2646,2650,2652,2738,2740,2744,2758,2762,3118,3158,3162,3164,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9700 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9700 48 4
  · have he : independentCachedBranchMembers9700.erase 48=independentCachedBranchMembers9698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9698
  · have he : independentCachedBranchMembers9700.filter (independentCachedEdge 48)=independentCachedBranchMembers9699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9699
def independentCachedBranchMembers9701 : Finset ℕ := ([36,48,66,72,160,190,192,222,1582,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9701 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9701 1582 5
  · have he : independentCachedBranchMembers9701.erase 1582=independentCachedBranchMembers9691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9691
  · have he : independentCachedBranchMembers9701.filter (independentCachedEdge 1582)=independentCachedBranchMembers9700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9700
def independentCachedBranchMembers9702 : Finset ℕ := ([48,72,192,1590,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2762,3126,3130,3132,3150,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9702 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9702 5 (fun x => (if x<2618 then (if x<1716 then (if x<192 then (if x<72 then 0 else 0) else (if x<1590 then 1 else (if x<1714 then 0 else 2))) else (if x<1738 then (if x<1720 then 3 else (if x<1734 then 4 else 1)) else (if x<1740 then 2 else (if x<2614 then 3 else 2)))) else (if x<3126 then (if x<2638 then (if x<2620 then 1 else 4) else (if x<2738 then 2 else (if x<2762 then 0 else 0))) else (if x<3150 then (if x<3130 then 3 else (if x<3132 then 4 else 1)) else (if x<3252 then 3 else (if x<3276 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9703 : Finset ℕ := ([72,192,1734,1738,1740,2638,2762,3150,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9703 4 (fun x => (if x<1740 then (if x<1734 then (if x<192 then 0 else 1) else (if x<1738 then 1 else 0)) else (if x<2762 then (if x<2638 then 2 else 0) else (if x<3150 then 1 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9704 : Finset ℕ := ([48,72,190,192,1590,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2762,3126,3130,3132,3150,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9704 190 4
  · have he : independentCachedBranchMembers9704.erase 190=independentCachedBranchMembers9702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9702
  · have he : independentCachedBranchMembers9704.filter (independentCachedEdge 190)=independentCachedBranchMembers9703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9703
def independentCachedBranchMembers9705 : Finset ℕ := ([190,1714,1720,1738,2618,2738,2762,3126,3132,3150,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9705 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9705 4 (fun x => (if x<2762 then (if x<1738 then (if x<1714 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2738 then 0 else 2))) else (if x<3150 then (if x<3126 then 2 else (if x<3132 then 0 else 1)) else (if x<3252 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9706 : Finset ℕ := ([48,72,190,192,1590,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2762,3126,3130,3132,3150,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9706 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9706 3274 4
  · have he : independentCachedBranchMembers9706.erase 3274=independentCachedBranchMembers9704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9704
  · have he : independentCachedBranchMembers9706.filter (independentCachedEdge 3274)=independentCachedBranchMembers9705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9705
def independentCachedBranchMembers9707 : Finset ℕ := ([72,192,1590,1720,1738,1740,2614,2762,3130,3132,3150,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9707 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9707 4 (fun x => (if x<2614 then (if x<1720 then (if x<192 then 0 else (if x<1590 then 1 else 0)) else (if x<1738 then 2 else (if x<1740 then 1 else 2))) else (if x<3132 then (if x<2762 then 1 else (if x<3130 then 0 else 2)) else (if x<3150 then 1 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9708 : Finset ℕ := ([48,72,190,192,1590,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2762,3126,3130,3132,3150,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9708 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9708 3256 4
  · have he : independentCachedBranchMembers9708.erase 3256=independentCachedBranchMembers9706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9706
  · have he : independentCachedBranchMembers9708.filter (independentCachedEdge 3256)=independentCachedBranchMembers9707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9707
def independentCachedBranchMembers9709 : Finset ℕ := ([72,190,1590,1714,1716,1734,2618,2620,2638,2762,3126,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9709 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9709 4 (fun x => (if x<2618 then (if x<1714 then (if x<190 then 0 else (if x<1590 then 1 else 0)) else (if x<1716 then 1 else (if x<1734 then 2 else 2))) else (if x<2762 then (if x<2620 then 1 else (if x<2638 then 2 else 2)) else (if x<3126 then 0 else (if x<3252 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9710 : Finset ℕ := ([48,72,190,192,1590,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2758,2762,3126,3130,3132,3150,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9710 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9710 2758 4
  · have he : independentCachedBranchMembers9710.erase 2758=independentCachedBranchMembers9708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9708
  · have he : independentCachedBranchMembers9710.filter (independentCachedEdge 2758)=independentCachedBranchMembers9709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9709
def independentCachedBranchMembers9711 : Finset ℕ := ([192,1716,1734,1740,2614,2620,2638,2738,2762,3130,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9711 4 (fun x => (if x<2638 then (if x<1740 then (if x<1716 then 0 else (if x<1734 then 1 else 0)) else (if x<2614 then 1 else (if x<2620 then 1 else 0))) else (if x<3130 then (if x<2738 then 1 else (if x<2762 then 2 else 2)) else (if x<3252 then 0 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9712 : Finset ℕ := ([48,72,190,192,1590,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2740,2758,2762,3126,3130,3132,3150,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9712 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9712 2740 4
  · have he : independentCachedBranchMembers9712.erase 2740=independentCachedBranchMembers9710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9710
  · have he : independentCachedBranchMembers9712.filter (independentCachedEdge 2740)=independentCachedBranchMembers9711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9711
def independentCachedBranchMembers9713 : Finset ℕ := ([72,1590,1716,1720,1734,1738,2620,2638,2738,3132,3150,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9713 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9713 4 (fun x => (if x<2620 then (if x<1720 then (if x<1590 then 0 else (if x<1716 then 0 else 1)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<3132 then (if x<2638 then 1 else (if x<2738 then 1 else 0)) else (if x<3150 then 2 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9714 : Finset ℕ := ([48,72,190,192,1590,1596,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2740,2758,2762,3126,3130,3132,3150,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9714 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9714 1596 4
  · have he : independentCachedBranchMembers9714.erase 1596=independentCachedBranchMembers9712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9712
  · have he : independentCachedBranchMembers9714.filter (independentCachedEdge 1596)=independentCachedBranchMembers9713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9713
def independentCachedBranchMembers9715 : Finset ℕ := ([72,190,192,1590,1714,1740,2614,2618,2738,3126,3130,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9715 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9715 4 (fun x => (if x<2614 then (if x<1590 then (if x<190 then 0 else (if x<192 then 1 else 2)) else (if x<1714 then 0 else (if x<1740 then 1 else 2))) else (if x<3126 then (if x<2618 then 1 else (if x<2738 then 2 else 0)) else (if x<3130 then 2 else (if x<3276 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9716 : Finset ℕ := ([48,66,72,190,192,1590,1596,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2740,2758,2762,3126,3130,3132,3150,3252,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9716 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9716 66 4
  · have he : independentCachedBranchMembers9716.erase 66=independentCachedBranchMembers9714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9714
  · have he : independentCachedBranchMembers9716.filter (independentCachedEdge 66)=independentCachedBranchMembers9715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9715
def independentCachedBranchMembers9717 : Finset ℕ := ([72,190,1590,1714,1716,1734,2614,2738,2740,2758,3130,3132,3150,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9717 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9717 4 (fun x => (if x<2740 then (if x<1716 then (if x<1590 then (if x<190 then 0 else 1) else (if x<1714 then 0 else 1)) else (if x<2614 then (if x<1734 then 2 else 2) else (if x<2738 then 1 else 0))) else (if x<3150 then (if x<3130 then (if x<2758 then 3 else 3) else (if x<3132 then 1 else 2)) else (if x<3274 then (if x<3256 then 2 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9718 : Finset ℕ := ([48,66,72,190,192,1590,1596,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2740,2758,2762,3126,3130,3132,3150,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9718 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9718 3270 4
  · have he : independentCachedBranchMembers9718.erase 3270=independentCachedBranchMembers9716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9716
  · have he : independentCachedBranchMembers9718.filter (independentCachedEdge 3270)=independentCachedBranchMembers9717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9717
def independentCachedBranchMembers9719 : Finset ℕ := ([72,192,1590,1720,1738,1740,2618,2620,2638,2738,2740,2758,3126,3256,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9719 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9719 4 (fun x => (if x<2638 then (if x<1738 then (if x<1590 then (if x<192 then 0 else 1) else (if x<1720 then 0 else 2)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2620 then 2 else 1))) else (if x<3126 then (if x<2740 then (if x<2738 then 2 else 0) else (if x<2758 then 3 else 3)) else (if x<3274 then (if x<3256 then 1 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9720 : Finset ℕ := ([48,66,72,190,192,1590,1596,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2740,2744,2758,2762,3126,3130,3132,3150,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9720 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9720 2744 4
  · have he : independentCachedBranchMembers9720.erase 2744=independentCachedBranchMembers9718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9718
  · have he : independentCachedBranchMembers9720.filter (independentCachedEdge 2744)=independentCachedBranchMembers9719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9719
def independentCachedBranchMembers9721 : Finset ℕ := ([192,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,3126,3130,3132,3150] : List ℕ).toFinset
theorem independentCachedBranchBound9721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9721 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9721 4 (fun x => (if x<2614 then (if x<1720 then (if x<1714 then 0 else (if x<1716 then 1 else 2)) else (if x<1738 then (if x<1734 then 3 else 0) else (if x<1740 then 1 else 2))) else (if x<3126 then (if x<2620 then (if x<2618 then 1 else 0) else (if x<2638 then 3 else 1)) else (if x<3132 then (if x<3130 then 2 else 3) else (if x<3150 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9722 : Finset ℕ := ([192,1734,1738,1740,2638,3150] : List ℕ).toFinset
theorem independentCachedBranchBound9722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9722 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9722 3 (fun x => (if x<1740 then (if x<1734 then 0 else (if x<1738 then 0 else 1)) else (if x<2638 then 2 else (if x<3150 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9723 : Finset ℕ := ([190,192,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,3126,3130,3132,3150] : List ℕ).toFinset
theorem independentCachedBranchBound9723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9723 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9723 190 3
  · have he : independentCachedBranchMembers9723.erase 190=independentCachedBranchMembers9721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9721
  · have he : independentCachedBranchMembers9723.filter (independentCachedEdge 190)=independentCachedBranchMembers9722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9722
def independentCachedBranchMembers9724 : Finset ℕ := ([48,66,72,190,192,1590,1596,1614,1714,1716,1720,1734,1738,1740,2614,2618,2620,2638,2738,2740,2744,2758,2762,3126,3130,3132,3150,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9724 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9724 1614 4
  · have he : independentCachedBranchMembers9724.erase 1614=independentCachedBranchMembers9720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9720
  · have he : independentCachedBranchMembers9724.filter (independentCachedEdge 1614)=independentCachedBranchMembers9723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9723
def independentCachedBranchMembers9725 : Finset ℕ := ([36,48,66,72,80,160,190,192,222,1582,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9725 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9725 80 5
  · have he : independentCachedBranchMembers9725.erase 80=independentCachedBranchMembers9701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9701
  · have he : independentCachedBranchMembers9725.filter (independentCachedEdge 80)=independentCachedBranchMembers9724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9724
def independentCachedBranchMembers9726 : Finset ℕ := ([48,72,160,222,1614,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2762,3126,3150,3162,3164,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9726 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9726 5 (fun x => (if x<2614 then (if x<1702 then (if x<160 then (if x<72 then 0 else 0) else (if x<222 then 1 else (if x<1614 then 2 else 0))) else (if x<1738 then (if x<1714 then 1 else (if x<1716 then 3 else 4)) else (if x<1740 then 2 else (if x<1752 then 4 else 3)))) else (if x<3126 then (if x<2652 then (if x<2638 then 3 else (if x<2650 then 2 else 1)) else (if x<2738 then 3 else (if x<2762 then 0 else 0))) else (if x<3164 then (if x<3150 then 4 else (if x<3162 then 4 else 2)) else (if x<3252 then 1 else (if x<3276 then 0 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9727 : Finset ℕ := ([160,1702,1714,1738,2652,2738,2762,3126,3150,3162,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9727 4 (fun x => (if x<2762 then (if x<1738 then (if x<1702 then 0 else (if x<1714 then 0 else 1)) else (if x<2652 then 1 else (if x<2738 then 0 else 2))) else (if x<3162 then (if x<3126 then 2 else (if x<3150 then 1 else 1)) else (if x<3252 then 0 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
