/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch216
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9728 : Finset ℕ := ([48,72,160,222,1614,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2762,3126,3150,3162,3164,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9728 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9728 3274 4
  · have he : independentCachedBranchMembers9728.erase 3274=independentCachedBranchMembers9726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9726
  · have he : independentCachedBranchMembers9728.filter (independentCachedEdge 3274)=independentCachedBranchMembers9727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9727
def independentCachedBranchMembers9729 : Finset ℕ := ([48,222,1614,1702,1738,1740,2638,2762,3126,3162,3164,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9729 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9729 4 (fun x => (if x<2638 then (if x<1702 then (if x<222 then 0 else (if x<1614 then 1 else 0)) else (if x<1738 then 2 else (if x<1740 then 1 else 2))) else (if x<3162 then (if x<2762 then 1 else (if x<3126 then 0 else 2)) else (if x<3164 then 1 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9730 : Finset ℕ := ([48,72,160,222,1614,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2762,3126,3150,3162,3164,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9730 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9730 3238 4
  · have he : independentCachedBranchMembers9730.erase 3238=independentCachedBranchMembers9728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9728
  · have he : independentCachedBranchMembers9730.filter (independentCachedEdge 3238)=independentCachedBranchMembers9729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9729
def independentCachedBranchMembers9731 : Finset ℕ := ([48,160,1614,1714,1716,1752,2614,2650,2652,2762,3150,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9731 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9731 4 (fun x => (if x<2614 then (if x<1714 then (if x<160 then 0 else (if x<1614 then 1 else 0)) else (if x<1716 then 1 else (if x<1752 then 2 else 2))) else (if x<2762 then (if x<2650 then 2 else (if x<2652 then 2 else 1)) else (if x<3150 then 0 else (if x<3252 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9732 : Finset ℕ := ([48,72,160,222,1614,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2762,2776,3126,3150,3162,3164,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9732 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9732 2776 4
  · have he : independentCachedBranchMembers9732.erase 2776=independentCachedBranchMembers9730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9730
  · have he : independentCachedBranchMembers9732.filter (independentCachedEdge 2776)=independentCachedBranchMembers9731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9731
def independentCachedBranchMembers9733 : Finset ℕ := ([222,1716,1740,1752,2614,2638,2650,2738,2762,3164,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9733 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9733 4 (fun x => (if x<2650 then (if x<1752 then (if x<1716 then 0 else (if x<1740 then 1 else 0)) else (if x<2614 then 1 else (if x<2638 then 1 else 0))) else (if x<3164 then (if x<2738 then 1 else (if x<2762 then 2 else 2)) else (if x<3252 then 0 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9734 : Finset ℕ := ([48,72,160,222,1614,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2740,2762,2776,3126,3150,3162,3164,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9734 2740 4
  · have he : independentCachedBranchMembers9734.erase 2740=independentCachedBranchMembers9732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9732
  · have he : independentCachedBranchMembers9734.filter (independentCachedEdge 2740)=independentCachedBranchMembers9733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9733
def independentCachedBranchMembers9735 : Finset ℕ := ([48,1614,1702,1716,1738,1752,2614,2650,2738,3126,3162,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9735 4 (fun x => (if x<2614 then (if x<1716 then (if x<1614 then 0 else (if x<1702 then 0 else 1)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<3126 then (if x<2650 then 1 else (if x<2738 then 1 else 0)) else (if x<3162 then 2 else (if x<3276 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9736 : Finset ℕ := ([48,72,160,222,1614,1626,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2740,2762,2776,3126,3150,3162,3164,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9736 1626 4
  · have he : independentCachedBranchMembers9736.erase 1626=independentCachedBranchMembers9734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9734
  · have he : independentCachedBranchMembers9736.filter (independentCachedEdge 1626)=independentCachedBranchMembers9735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9735
def independentCachedBranchMembers9737 : Finset ℕ := ([48,160,222,1614,1714,1740,2638,2652,2738,3150,3164,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9737 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9737 4 (fun x => (if x<2638 then (if x<1614 then (if x<160 then 0 else (if x<222 then 1 else 2)) else (if x<1714 then 0 else (if x<1740 then 1 else 2))) else (if x<3150 then (if x<2652 then 1 else (if x<2738 then 2 else 0)) else (if x<3164 then 2 else (if x<3276 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9738 : Finset ℕ := ([36,48,72,160,222,1614,1626,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2740,2762,2776,3126,3150,3162,3164,3238,3252,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9738 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9738 36 4
  · have he : independentCachedBranchMembers9738.erase 36=independentCachedBranchMembers9736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9736
  · have he : independentCachedBranchMembers9738.filter (independentCachedEdge 36)=independentCachedBranchMembers9737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9737
def independentCachedBranchMembers9739 : Finset ℕ := ([48,160,1614,1714,1716,1752,2638,2738,2740,2776,3126,3162,3164,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9739 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9739 4 (fun x => (if x<2740 then (if x<1716 then (if x<1614 then (if x<160 then 0 else 1) else (if x<1714 then 0 else 1)) else (if x<2638 then (if x<1752 then 2 else 2) else (if x<2738 then 1 else 0))) else (if x<3164 then (if x<3126 then (if x<2776 then 3 else 3) else (if x<3162 then 2 else 2)) else (if x<3274 then (if x<3238 then 1 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9740 : Finset ℕ := ([36,48,72,160,222,1614,1626,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2738,2740,2762,2776,3126,3150,3162,3164,3238,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9740 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9740 3288 4
  · have he : independentCachedBranchMembers9740.erase 3288=independentCachedBranchMembers9738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9738
  · have he : independentCachedBranchMembers9740.filter (independentCachedEdge 3288)=independentCachedBranchMembers9739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9739
def independentCachedBranchMembers9741 : Finset ℕ := ([48,222,1614,1702,1738,1740,2614,2650,2652,2738,2740,2776,3150,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9741 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9741 4 (fun x => (if x<2652 then (if x<1738 then (if x<1614 then (if x<222 then 0 else 1) else (if x<1702 then 0 else 2)) else (if x<2614 then (if x<1740 then 1 else 2) else (if x<2650 then 2 else 1))) else (if x<3150 then (if x<2740 then (if x<2738 then 2 else 0) else (if x<2776 then 3 else 3)) else (if x<3274 then (if x<3238 then 1 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9742 : Finset ℕ := ([36,48,72,160,222,1614,1626,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2726,2738,2740,2762,2776,3126,3150,3162,3164,3238,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9742 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9742 2726 4
  · have he : independentCachedBranchMembers9742.erase 2726=independentCachedBranchMembers9740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9740
  · have he : independentCachedBranchMembers9742.filter (independentCachedEdge 2726)=independentCachedBranchMembers9741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9741
def independentCachedBranchMembers9743 : Finset ℕ := ([160,222,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,3126,3150,3162,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9743 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9743 4 (fun x => (if x<2614 then (if x<1716 then (if x<1702 then (if x<222 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<1740 then (if x<1738 then 3 else 1) else (if x<1752 then 3 else 2))) else (if x<3126 then (if x<2650 then (if x<2638 then 2 else 1) else (if x<2652 then 0 else 2)) else (if x<3162 then (if x<3150 then 3 else 3) else (if x<3164 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9744 : Finset ℕ := ([36,48,72,160,222,1590,1614,1626,1702,1714,1716,1738,1740,1752,2614,2638,2650,2652,2726,2738,2740,2762,2776,3126,3150,3162,3164,3238,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9744 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9744 1590 4
  · have he : independentCachedBranchMembers9744.erase 1590=independentCachedBranchMembers9742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9742
  · have he : independentCachedBranchMembers9744.filter (independentCachedEdge 1590)=independentCachedBranchMembers9743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9743
def independentCachedBranchMembers9745 : Finset ℕ := ([36,40,48,66,72,80,160,190,192,222,1582,1590,1596,1614,1622,1626,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2732,2738,2740,2744,2758,2762,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3252,3256,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9745 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9745 40 5
  · have he : independentCachedBranchMembers9745.erase 40=independentCachedBranchMembers9725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9725
  · have he : independentCachedBranchMembers9745.filter (independentCachedEdge 40)=independentCachedBranchMembers9744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9744
def independentCachedBranchMembers9746 : Finset ℕ := ([160,190,1590,1614,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2738,2744,2772,3118,3130,3158,3164,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9746 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9746 5 (fun x => (if x<2650 then (if x<1714 then (if x<1614 then (if x<190 then 0 else (if x<1590 then 0 else 1)) else (if x<1702 then 1 else (if x<1708 then 0 else 1))) else (if x<1748 then (if x<1720 then 2 else (if x<1738 then 0 else 2)) else (if x<2620 then (if x<2614 then 1 else 2) else (if x<2638 then 3 else 2)))) else (if x<3158 then (if x<2744 then (if x<2726 then 3 else (if x<2738 then 4 else 0)) else (if x<3118 then (if x<2772 then 4 else 3) else (if x<3130 then 1 else 3))) else (if x<3252 then (if x<3164 then 1 else (if x<3242 then 3 else 0)) else (if x<3276 then (if x<3270 then 0 else 4) else (if x<3288 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9747 : Finset ℕ := ([190,1708,1720,1748,2620,2744,2772,3118,3130,3158,3242,3270] : List ℕ).toFinset
theorem independentCachedBranchBound9747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9747 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9747 4 (fun x => (if x<2772 then (if x<1748 then (if x<1708 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2744 then 0 else 2))) else (if x<3158 then (if x<3118 then 2 else (if x<3130 then 0 else 1)) else (if x<3242 then 1 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9748 : Finset ℕ := ([72,160,190,1590,1614,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2738,2744,2772,3118,3130,3158,3164,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9748 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9748 72 4
  · have he : independentCachedBranchMembers9748.erase 72=independentCachedBranchMembers9746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9746
  · have he : independentCachedBranchMembers9748.filter (independentCachedEdge 72)=independentCachedBranchMembers9747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9747
def independentCachedBranchMembers9749 : Finset ℕ := ([160,1702,1708,1748,2650,2726,2772,3118,3158,3164,3242,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9749 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9749 4 (fun x => (if x<2772 then (if x<1748 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<2650 then 1 else (if x<2726 then 0 else 2))) else (if x<3164 then (if x<3118 then 2 else (if x<3158 then 1 else 1)) else (if x<3242 then 0 else (if x<3288 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9750 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2738,2744,2772,3118,3130,3158,3164,3242,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9750 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9750 48 4
  · have he : independentCachedBranchMembers9750.erase 48=independentCachedBranchMembers9748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9748
  · have he : independentCachedBranchMembers9750.filter (independentCachedEdge 48)=independentCachedBranchMembers9749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9749
def independentCachedBranchMembers9751 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1720,2614,2638,2726,2744,3118,3158,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9751 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9751 4 (fun x => (if x<2614 then (if x<1590 then (if x<160 then (if x<72 then 0 else 0) else (if x<190 then 1 else 1)) else (if x<1702 then (if x<1614 then 0 else 0) else (if x<1720 then 1 else 1))) else (if x<3118 then (if x<2726 then (if x<2638 then 2 else 2) else (if x<2744 then 3 else 3)) else (if x<3270 then (if x<3158 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9752 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2738,2744,2772,3118,3130,3158,3164,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9752 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9752 3282 4
  · have he : independentCachedBranchMembers9752.erase 3282=independentCachedBranchMembers9750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9750
  · have he : independentCachedBranchMembers9752.filter (independentCachedEdge 3282)=independentCachedBranchMembers9751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9751
def independentCachedBranchMembers9753 : Finset ℕ := ([160,190,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,3118,3130,3158,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9753 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9753 4 (fun x => (if x<2614 then (if x<1714 then (if x<1702 then (if x<190 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1738 then (if x<1720 then 1 else 0) else (if x<1748 then 1 else 1))) else (if x<3118 then (if x<2638 then (if x<2620 then 2 else 3) else (if x<2650 then 2 else 3)) else (if x<3158 then (if x<3130 then 2 else 3) else (if x<3164 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9754 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2738,2744,2762,2772,3118,3130,3158,3164,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9754 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9754 2762 4
  · have he : independentCachedBranchMembers9754.erase 2762=independentCachedBranchMembers9752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9752
  · have he : independentCachedBranchMembers9754.filter (independentCachedEdge 2762)=independentCachedBranchMembers9753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9753
def independentCachedBranchMembers9755 : Finset ℕ := ([48,72,1590,1614,1708,1714,1738,1748,2620,2650,2726,2744,3130,3164,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9755 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9755 4 (fun x => (if x<2620 then (if x<1708 then (if x<1590 then (if x<72 then 0 else 0) else (if x<1614 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<1748 then 1 else 1))) else (if x<3130 then (if x<2726 then (if x<2650 then 2 else 2) else (if x<2744 then 3 else 3)) else (if x<3270 then (if x<3164 then 2 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9756 : Finset ℕ := ([48,72,160,190,1590,1614,1702,1708,1714,1720,1738,1748,2614,2620,2638,2650,2726,2732,2738,2744,2762,2772,3118,3130,3158,3164,3242,3252,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9756 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9756 2732 4
  · have he : independentCachedBranchMembers9756.erase 2732=independentCachedBranchMembers9754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9754
  · have he : independentCachedBranchMembers9756.filter (independentCachedEdge 2732)=independentCachedBranchMembers9755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9755
def independentCachedBranchMembers9757 : Finset ℕ := ([190,1614,1702,1708,1738,2614,2620,2650,2738,2744,2772,3118,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9757 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9757 4 (fun x => (if x<2650 then (if x<1708 then (if x<1614 then 0 else (if x<1702 then 1 else 0)) else (if x<2614 then (if x<1738 then 1 else 2) else (if x<2620 then 0 else 2))) else (if x<3118 then (if x<2744 then (if x<2738 then 1 else 3) else (if x<2772 then 1 else 3)) else (if x<3270 then (if x<3242 then 0 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9758 : Finset ℕ := ([1702,1708,2650,2772,3118,3242] : List ℕ).toFinset
theorem independentCachedBranchBound9758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9758 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9758 3 (fun x => (if x<2772 then (if x<1708 then 0 else (if x<2650 then 1 else 0)) else (if x<3118 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9759 : Finset ℕ := ([48,190,1614,1702,1708,1738,2614,2620,2650,2738,2744,2772,3118,3242,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9759 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9759 48 3
  · have he : independentCachedBranchMembers9759.erase 48=independentCachedBranchMembers9757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9757
  · have he : independentCachedBranchMembers9759.filter (independentCachedEdge 48)=independentCachedBranchMembers9758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9758
end EntropyDesigns.QuadraticRefinement
