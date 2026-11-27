/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch217
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9760 : Finset ℕ := ([48,72,160,190,1590,1614,1626,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2732,2738,2744,2762,2772,3118,3130,3158,3164,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9760 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9760 1626 4
  · have he : independentCachedBranchMembers9760.erase 1626=independentCachedBranchMembers9756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9756
  · have he : independentCachedBranchMembers9760.filter (independentCachedEdge 1626)=independentCachedBranchMembers9759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9759
def independentCachedBranchMembers9761 : Finset ℕ := ([160,1590,1708,1720,1738,2620,2638,2650,2726,2738,2772,3158,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9761 4 (fun x => (if x<2650 then (if x<1720 then (if x<1590 then 0 else (if x<1708 then 1 else 0)) else (if x<2620 then (if x<1738 then 1 else 2) else (if x<2638 then 1 else 2))) else (if x<3158 then (if x<2738 then (if x<2726 then 0 else 3) else (if x<2772 then 1 else 3)) else (if x<3276 then (if x<3242 then 0 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9762 : Finset ℕ := ([1708,1720,2620,2772,3158,3242] : List ℕ).toFinset
theorem independentCachedBranchBound9762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9762 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9762 3 (fun x => (if x<2772 then (if x<1720 then 0 else (if x<2620 then 1 else 0)) else (if x<3158 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9763 : Finset ℕ := ([72,160,1590,1708,1720,1738,2620,2638,2650,2726,2738,2772,3158,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9763 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9763 72 3
  · have he : independentCachedBranchMembers9763.erase 72=independentCachedBranchMembers9761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9761
  · have he : independentCachedBranchMembers9763.filter (independentCachedEdge 72)=independentCachedBranchMembers9762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9762
def independentCachedBranchMembers9764 : Finset ℕ := ([48,72,160,190,1590,1596,1614,1626,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2732,2738,2744,2762,2772,3118,3130,3158,3164,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9764 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9764 1596 4
  · have he : independentCachedBranchMembers9764.erase 1596=independentCachedBranchMembers9760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9760
  · have he : independentCachedBranchMembers9764.filter (independentCachedEdge 1596)=independentCachedBranchMembers9763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9763
def independentCachedBranchMembers9765 : Finset ℕ := ([72,190,1590,1702,1714,1748,2614,2726,2738,2772,3118,3130,3164,3242,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9765 4 (fun x => (if x<2738 then (if x<1714 then (if x<1590 then (if x<190 then 0 else 1) else (if x<1702 then 0 else 1)) else (if x<2614 then (if x<1748 then 2 else 2) else (if x<2726 then 1 else 0))) else (if x<3164 then (if x<3118 then (if x<2772 then 3 else 3) else (if x<3130 then 1 else 2)) else (if x<3276 then (if x<3242 then 2 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9766 : Finset ℕ := ([48,66,72,160,190,1590,1596,1614,1626,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2732,2738,2744,2762,2772,3118,3130,3158,3164,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9766 66 4
  · have he : independentCachedBranchMembers9766.erase 66=independentCachedBranchMembers9764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9764
  · have he : independentCachedBranchMembers9766.filter (independentCachedEdge 66)=independentCachedBranchMembers9765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9765
def independentCachedBranchMembers9767 : Finset ℕ := ([48,160,1614,1714,1720,1748,2638,2738,2744,2772,3130,3158,3164,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9767 4 (fun x => (if x<2744 then (if x<1720 then (if x<1614 then (if x<160 then 0 else 1) else (if x<1714 then 0 else 1)) else (if x<2638 then (if x<1748 then 2 else 2) else (if x<2738 then 1 else 0))) else (if x<3164 then (if x<3130 then (if x<2772 then 3 else 3) else (if x<3158 then 2 else 2)) else (if x<3270 then (if x<3242 then 1 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9768 : Finset ℕ := ([36,48,66,72,160,190,1590,1596,1614,1626,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2732,2738,2744,2762,2772,3118,3130,3158,3164,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9768 36 4
  · have he : independentCachedBranchMembers9768.erase 36=independentCachedBranchMembers9766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9766
  · have he : independentCachedBranchMembers9768.filter (independentCachedEdge 36)=independentCachedBranchMembers9767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9767
def independentCachedBranchMembers9769 : Finset ℕ := ([36,40,48,66,72,80,160,190,192,222,1582,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9769 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9769 3284 5
  · have he : independentCachedBranchMembers9769.erase 3284=independentCachedBranchMembers9745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9745
  · have he : independentCachedBranchMembers9769.filter (independentCachedEdge 3284)=independentCachedBranchMembers9768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9768
def independentCachedBranchMembers9770 : Finset ℕ := ([80,192,222,1582,1622,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2738,2758,2772,2776,3126,3130,3150,3164,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9770 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9770 5 (fun x => (if x<2650 then (if x<1734 then (if x<1582 then (if x<192 then 0 else (if x<222 then 1 else 0)) else (if x<1708 then (if x<1622 then 1 else 0) else (if x<1714 then 2 else 2))) else (if x<1752 then (if x<1738 then 1 else (if x<1748 then 2 else 2)) else (if x<2620 then (if x<2606 then 0 else 3) else (if x<2646 then 1 else 3)))) else (if x<3150 then (if x<2772 then (if x<2738 then 0 else (if x<2758 then 3 else 4)) else (if x<3126 then (if x<2776 then 0 else 4) else (if x<3130 then 3 else 1))) else (if x<3242 then (if x<3164 then 3 else (if x<3238 then 0 else 4)) else (if x<3276 then (if x<3256 then 2 else 4) else (if x<3282 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9771 : Finset ℕ := ([222,1714,1738,1752,2650,2738,2776,3126,3150,3164,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9771 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9771 4 (fun x => (if x<2776 then (if x<1752 then (if x<1714 then 0 else (if x<1738 then 1 else 0)) else (if x<2650 then 1 else (if x<2738 then 0 else 2))) else (if x<3164 then (if x<3126 then 2 else (if x<3150 then 1 else 0)) else (if x<3238 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9772 : Finset ℕ := ([40,80,192,222,1582,1622,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2738,2758,2772,2776,3126,3130,3150,3164,3238,3242,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9772 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9772 40 4
  · have he : independentCachedBranchMembers9772.erase 40=independentCachedBranchMembers9770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9770
  · have he : independentCachedBranchMembers9772.filter (independentCachedEdge 40)=independentCachedBranchMembers9771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9771
def independentCachedBranchMembers9773 : Finset ℕ := ([40,80,192,222,1582,1622,1734,1752,2606,2646,2758,2776,3126,3150,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9773 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9773 4 (fun x => (if x<2606 then (if x<1582 then (if x<192 then (if x<80 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1734 then (if x<1622 then 0 else 0) else (if x<1752 then 1 else 1))) else (if x<3126 then (if x<2758 then (if x<2646 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3150 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9774 : Finset ℕ := ([40,80,192,222,1582,1622,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2738,2758,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9774 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9774 3252 4
  · have he : independentCachedBranchMembers9774.erase 3252=independentCachedBranchMembers9772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9772
  · have he : independentCachedBranchMembers9774.filter (independentCachedEdge 3252)=independentCachedBranchMembers9773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9773
def independentCachedBranchMembers9775 : Finset ℕ := ([40,80,1582,1622,1708,1714,1738,1748,2620,2650,2758,2776,3130,3164,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound9775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9775 4 (fun x => (if x<2620 then (if x<1708 then (if x<1582 then (if x<80 then 0 else 0) else (if x<1622 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3130 then (if x<2758 then (if x<2650 then 2 else 2) else (if x<2776 then 3 else 3)) else (if x<3238 then (if x<3164 then 2 else 2) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9776 : Finset ℕ := ([40,80,192,222,1582,1622,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2738,2758,2762,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9776 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9776 2762 4
  · have he : independentCachedBranchMembers9776.erase 2762=independentCachedBranchMembers9774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9774
  · have he : independentCachedBranchMembers9776.filter (independentCachedEdge 2762)=independentCachedBranchMembers9775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9775
def independentCachedBranchMembers9777 : Finset ℕ := ([192,222,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,3126,3130,3150,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9777 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9777 4 (fun x => (if x<2606 then (if x<1734 then (if x<1708 then (if x<222 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3126 then (if x<2646 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<3150 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9778 : Finset ℕ := ([40,80,192,222,1582,1622,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9778 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9778 2732 4
  · have he : independentCachedBranchMembers9778.erase 2732=independentCachedBranchMembers9776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9776
  · have he : independentCachedBranchMembers9778.filter (independentCachedEdge 2732)=independentCachedBranchMembers9777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9777
def independentCachedBranchMembers9779 : Finset ℕ := ([192,1622,1708,1738,1752,2606,2620,2650,2738,2758,2772,3126,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9779 4 (fun x => (if x<2650 then (if x<1738 then (if x<1622 then 0 else (if x<1708 then 1 else 2)) else (if x<2606 then (if x<1752 then 0 else 1) else (if x<2620 then 2 else 0))) else (if x<3126 then (if x<2758 then (if x<2738 then 1 else 3) else (if x<2772 then 3 else 1)) else (if x<3256 then (if x<3242 then 0 else 2) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9780 : Finset ℕ := ([1738,1752,2650,2738,3126,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9780 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9780 3 (fun x => (if x<2738 then (if x<1752 then 0 else (if x<2650 then 1 else 0)) else (if x<3126 then 2 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9781 : Finset ℕ := ([40,192,1622,1708,1738,1752,2606,2620,2650,2738,2758,2772,3126,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9781 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9781 40 3
  · have he : independentCachedBranchMembers9781.erase 40=independentCachedBranchMembers9779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9779
  · have he : independentCachedBranchMembers9781.filter (independentCachedEdge 40)=independentCachedBranchMembers9780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9780
def independentCachedBranchMembers9782 : Finset ℕ := ([40,80,192,222,1582,1622,1626,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9782 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9782 1626 4
  · have he : independentCachedBranchMembers9782.erase 1626=independentCachedBranchMembers9778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9778
  · have he : independentCachedBranchMembers9782.filter (independentCachedEdge 1626)=independentCachedBranchMembers9781 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9781
def independentCachedBranchMembers9783 : Finset ℕ := ([222,1582,1708,1734,1738,2620,2646,2650,2738,2772,2776,3150,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9783 4 (fun x => (if x<2650 then (if x<1734 then (if x<1582 then 0 else (if x<1708 then 1 else 2)) else (if x<2620 then (if x<1738 then 0 else 1) else (if x<2646 then 1 else 0))) else (if x<3150 then (if x<2772 then (if x<2738 then 2 else 3) else (if x<2776 then 3 else 1)) else (if x<3242 then (if x<3238 then 0 else 2) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9784 : Finset ℕ := ([1734,1738,2620,2738,3150,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9784 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9784 3 (fun x => (if x<2738 then (if x<1738 then 0 else (if x<2620 then 1 else 0)) else (if x<3150 then 2 else (if x<3276 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9785 : Finset ℕ := ([80,222,1582,1708,1734,1738,2620,2646,2650,2738,2772,2776,3150,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9785 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9785 80 3
  · have he : independentCachedBranchMembers9785.erase 80=independentCachedBranchMembers9783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9783
  · have he : independentCachedBranchMembers9785.filter (independentCachedEdge 80)=independentCachedBranchMembers9784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9784
def independentCachedBranchMembers9786 : Finset ℕ := ([40,80,192,222,1582,1596,1622,1626,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9786 1596 4
  · have he : independentCachedBranchMembers9786.erase 1596=independentCachedBranchMembers9782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9782
  · have he : independentCachedBranchMembers9786.filter (independentCachedEdge 1596)=independentCachedBranchMembers9785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9785
def independentCachedBranchMembers9787 : Finset ℕ := ([80,192,1582,1714,1748,1752,2606,2738,2772,2776,3126,3130,3164,3238,3242,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9787 4 (fun x => (if x<2772 then (if x<1748 then (if x<1582 then (if x<192 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<2606 then (if x<1752 then 1 else 2) else (if x<2738 then 1 else 3))) else (if x<3164 then (if x<3126 then (if x<2776 then 0 else 3) else (if x<3130 then 2 else 1)) else (if x<3242 then (if x<3238 then 2 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9788 : Finset ℕ := ([40,66,80,192,222,1582,1596,1622,1626,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9788 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9788 66 4
  · have he : independentCachedBranchMembers9788.erase 66=independentCachedBranchMembers9786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9786
  · have he : independentCachedBranchMembers9788.filter (independentCachedEdge 66)=independentCachedBranchMembers9787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9787
def independentCachedBranchMembers9789 : Finset ℕ := ([40,222,1622,1714,1734,1748,2646,2738,2758,2772,3130,3150,3164,3242,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9789 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9789 4 (fun x => (if x<2758 then (if x<1734 then (if x<1622 then (if x<222 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<2646 then (if x<1748 then 1 else 2) else (if x<2738 then 1 else 3))) else (if x<3164 then (if x<3130 then (if x<2772 then 0 else 3) else (if x<3150 then 2 else 1)) else (if x<3256 then (if x<3242 then 2 else 3) else (if x<3276 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9790 : Finset ℕ := ([36,40,66,80,192,222,1582,1596,1622,1626,1708,1714,1734,1738,1748,1752,2606,2620,2646,2650,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3238,3242,3252,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9790 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9790 36 4
  · have he : independentCachedBranchMembers9790.erase 36=independentCachedBranchMembers9788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9788
  · have he : independentCachedBranchMembers9790.filter (independentCachedEdge 36)=independentCachedBranchMembers9789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9789
def independentCachedBranchMembers9791 : Finset ℕ := ([36,40,48,66,72,80,160,190,192,222,1582,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9791 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9791 3250 5
  · have he : independentCachedBranchMembers9791.erase 3250=independentCachedBranchMembers9769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9769
  · have he : independentCachedBranchMembers9791.filter (independentCachedEdge 3250)=independentCachedBranchMembers9790 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9790
end EntropyDesigns.QuadraticRefinement
