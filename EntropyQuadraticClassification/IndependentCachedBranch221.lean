/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch220
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9856 : Finset ℕ := ([80,222,1582,1590,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2740,2770,2776,3130,3150,3158,3164,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9856 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9856 5 (fun x => (if x<2646 then (if x<1714 then (if x<1590 then (if x<222 then 0 else (if x<1582 then 0 else 1)) else (if x<1626 then 2 else (if x<1706 then 0 else 2))) else (if x<1740 then (if x<1720 then 1 else (if x<1734 then 3 else 1)) else (if x<2618 then (if x<1748 then 3 else 0) else (if x<2638 then 1 else 1)))) else (if x<3150 then (if x<2740 then (if x<2652 then 0 else (if x<2726 then 4 else 1)) else (if x<2776 then (if x<2770 then 4 else 1) else (if x<3130 then 0 else 2))) else (if x<3238 then (if x<3158 then 3 else (if x<3164 then 2 else 0)) else (if x<3274 then (if x<3244 then 2 else 3) else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9857 : Finset ℕ := ([222,1582,1590,1734,1740,1748,2618,2770,2776,3130,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9857 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9857 4 (fun x => (if x<2618 then (if x<1734 then (if x<1582 then 0 else (if x<1590 then 1 else 2)) else (if x<1740 then 0 else (if x<1748 then 1 else 2))) else (if x<3130 then (if x<2770 then 1 else (if x<2776 then 0 else 1)) else (if x<3274 then 2 else (if x<3288 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9858 : Finset ℕ := ([80,160,222,1582,1590,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2740,2770,2776,3130,3150,3158,3164,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9858 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9858 160 4
  · have he : independentCachedBranchMembers9858.erase 160=independentCachedBranchMembers9856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9856
  · have he : independentCachedBranchMembers9858.filter (independentCachedEdge 160)=independentCachedBranchMembers9857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9857
def independentCachedBranchMembers9859 : Finset ℕ := ([80,1582,1706,1720,1734,1748,2618,2646,2770,3130,3158,3244] : List ℕ).toFinset
theorem independentCachedBranchBound9859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9859 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9859 4 (fun x => (if x<2618 then (if x<1720 then (if x<1582 then 0 else (if x<1706 then 0 else 1)) else (if x<1734 then 2 else (if x<1748 then 1 else 2))) else (if x<3130 then (if x<2646 then 1 else (if x<2770 then 1 else 0)) else (if x<3158 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9860 : Finset ℕ := ([72,80,160,222,1582,1590,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2740,2770,2776,3130,3150,3158,3164,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9860 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9860 72 4
  · have he : independentCachedBranchMembers9860.erase 72=independentCachedBranchMembers9858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9858
  · have he : independentCachedBranchMembers9860.filter (independentCachedEdge 72)=independentCachedBranchMembers9859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9859
def independentCachedBranchMembers9861 : Finset ℕ := ([160,1590,1706,1720,1740,2618,2638,2652,2726,2740,2770,3158,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9861 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9861 4 (fun x => (if x<2652 then (if x<1720 then (if x<1590 then 0 else (if x<1706 then 1 else 0)) else (if x<2618 then (if x<1740 then 1 else 2) else (if x<2638 then 1 else 2))) else (if x<3158 then (if x<2740 then (if x<2726 then 0 else 3) else (if x<2770 then 1 else 3)) else (if x<3274 then (if x<3244 then 0 else 3) else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9862 : Finset ℕ := ([1706,1720,2618,2770,3158,3244] : List ℕ).toFinset
theorem independentCachedBranchBound9862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9862 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9862 3 (fun x => (if x<2770 then (if x<1720 then 0 else (if x<2618 then 1 else 0)) else (if x<3158 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9863 : Finset ℕ := ([72,160,1590,1706,1720,1740,2618,2638,2652,2726,2740,2770,3158,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9863 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9863 72 3
  · have he : independentCachedBranchMembers9863.erase 72=independentCachedBranchMembers9861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9861
  · have he : independentCachedBranchMembers9863.filter (independentCachedEdge 72)=independentCachedBranchMembers9862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9862
def independentCachedBranchMembers9864 : Finset ℕ := ([72,80,160,222,1582,1590,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2740,2770,2776,3130,3150,3158,3164,3238,3244,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9864 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9864 3282 4
  · have he : independentCachedBranchMembers9864.erase 3282=independentCachedBranchMembers9860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9860
  · have he : independentCachedBranchMembers9864.filter (independentCachedEdge 3282)=independentCachedBranchMembers9863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9863
def independentCachedBranchMembers9865 : Finset ℕ := ([222,1582,1706,1734,1740,2618,2646,2652,2740,2770,2776,3150,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9865 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9865 4 (fun x => (if x<2652 then (if x<1734 then (if x<1582 then 0 else (if x<1706 then 1 else 2)) else (if x<2618 then (if x<1740 then 0 else 1) else (if x<2646 then 1 else 0))) else (if x<3150 then (if x<2770 then (if x<2740 then 2 else 3) else (if x<2776 then 3 else 1)) else (if x<3244 then (if x<3238 then 0 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9866 : Finset ℕ := ([1734,1740,2618,2740,3150,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9866 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9866 3 (fun x => (if x<2740 then (if x<1740 then 0 else (if x<2618 then 1 else 0)) else (if x<3150 then 2 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9867 : Finset ℕ := ([80,222,1582,1706,1734,1740,2618,2646,2652,2740,2770,2776,3150,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9867 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9867 80 3
  · have he : independentCachedBranchMembers9867.erase 80=independentCachedBranchMembers9865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9865
  · have he : independentCachedBranchMembers9867.filter (independentCachedEdge 80)=independentCachedBranchMembers9866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9866
def independentCachedBranchMembers9868 : Finset ℕ := ([72,80,160,222,1582,1590,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2740,2770,2776,3130,3150,3158,3164,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9868 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9868 3252 4
  · have he : independentCachedBranchMembers9868.erase 3252=independentCachedBranchMembers9864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9864
  · have he : independentCachedBranchMembers9868.filter (independentCachedEdge 3252)=independentCachedBranchMembers9867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9867
def independentCachedBranchMembers9869 : Finset ℕ := ([80,160,1582,1714,1720,1748,2638,2740,2770,2776,3130,3158,3164,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9869 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9869 4 (fun x => (if x<2770 then (if x<1720 then (if x<1582 then (if x<160 then 0 else 0) else (if x<1714 then 1 else 1)) else (if x<2638 then (if x<1748 then 2 else 2) else (if x<2740 then 1 else 2))) else (if x<3164 then (if x<3130 then (if x<2776 then 1 else 2) else (if x<3158 then 3 else 0)) else (if x<3244 then (if x<3238 then 3 else 0) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9870 : Finset ℕ := ([72,80,160,222,1582,1590,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2740,2762,2770,2776,3130,3150,3158,3164,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9870 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9870 2762 4
  · have he : independentCachedBranchMembers9870.erase 2762=independentCachedBranchMembers9868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9868
  · have he : independentCachedBranchMembers9870.filter (independentCachedEdge 2762)=independentCachedBranchMembers9869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9869
def independentCachedBranchMembers9871 : Finset ℕ := ([72,222,1590,1714,1734,1748,2646,2726,2740,2770,3130,3150,3164,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9871 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9871 4 (fun x => (if x<2740 then (if x<1734 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1714 then 1 else 2)) else (if x<2646 then (if x<1748 then 1 else 2) else (if x<2726 then 1 else 1))) else (if x<3164 then (if x<3130 then (if x<2770 then 2 else 2) else (if x<3150 then 3 else 0)) else (if x<3274 then (if x<3244 then 3 else 3) else (if x<3288 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9872 : Finset ℕ := ([72,80,160,222,1582,1590,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2732,2740,2762,2770,2776,3130,3150,3158,3164,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9872 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9872 2732 4
  · have he : independentCachedBranchMembers9872.erase 2732=independentCachedBranchMembers9870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9870
  · have he : independentCachedBranchMembers9872.filter (independentCachedEdge 2732)=independentCachedBranchMembers9871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9871
def independentCachedBranchMembers9873 : Finset ℕ := ([72,80,160,222,1582,1590,1720,1734,2638,2646,2726,2776,3150,3158,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9873 4 (fun x => (if x<2638 then (if x<1582 then (if x<160 then (if x<80 then 0 else 1) else (if x<222 then 0 else 1)) else (if x<1720 then (if x<1590 then 2 else 3) else (if x<1734 then 2 else 3))) else (if x<3150 then (if x<2726 then (if x<2646 then 0 else 1) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3158 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9874 : Finset ℕ := ([72,80,160,222,1582,1590,1596,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2732,2740,2762,2770,2776,3130,3150,3158,3164,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9874 1596 4
  · have he : independentCachedBranchMembers9874.erase 1596=independentCachedBranchMembers9872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9872
  · have he : independentCachedBranchMembers9874.filter (independentCachedEdge 1596)=independentCachedBranchMembers9873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9873
def independentCachedBranchMembers9875 : Finset ℕ := ([72,80,1582,1590,1706,1714,1740,1748,2618,2652,2726,2776,3130,3164,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9875 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9875 4 (fun x => (if x<2618 then (if x<1706 then (if x<1582 then (if x<80 then 0 else 1) else (if x<1590 then 1 else 0)) else (if x<1740 then (if x<1714 then 2 else 3) else (if x<1748 then 2 else 3))) else (if x<3130 then (if x<2726 then (if x<2652 then 2 else 2) else (if x<2776 then 0 else 1)) else (if x<3238 then (if x<3164 then 3 else 3) else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9876 : Finset ℕ := ([66,72,80,160,222,1582,1590,1596,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2732,2740,2762,2770,2776,3130,3150,3158,3164,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9876 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9876 66 4
  · have he : independentCachedBranchMembers9876.erase 66=independentCachedBranchMembers9874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9874
  · have he : independentCachedBranchMembers9876.filter (independentCachedEdge 66)=independentCachedBranchMembers9875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9875
def independentCachedBranchMembers9877 : Finset ℕ := ([160,222,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,3130,3150,3158,3164] : List ℕ).toFinset
theorem independentCachedBranchBound9877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9877 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9877 4 (fun x => (if x<2618 then (if x<1720 then (if x<1706 then (if x<222 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<1740 then (if x<1734 then 3 else 1) else (if x<1748 then 3 else 2))) else (if x<3130 then (if x<2646 then (if x<2638 then 2 else 1) else (if x<2652 then 0 else 2)) else (if x<3158 then (if x<3150 then 3 else 3) else (if x<3164 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9878 : Finset ℕ := ([36,66,72,80,160,222,1582,1590,1596,1626,1706,1714,1720,1734,1740,1748,2618,2638,2646,2652,2726,2732,2740,2762,2770,2776,3130,3150,3158,3164,3238,3244,3252,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9878 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9878 36 4
  · have he : independentCachedBranchMembers9878.erase 36=independentCachedBranchMembers9876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9876
  · have he : independentCachedBranchMembers9878.filter (independentCachedEdge 36)=independentCachedBranchMembers9877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9877
def independentCachedBranchMembers9879 : Finset ℕ := ([36,40,48,66,72,80,160,190,192,222,1582,1590,1594,1596,1614,1622,1626,1628,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9879 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9879 1594 5
  · have he : independentCachedBranchMembers9879.erase 1594=independentCachedBranchMembers9855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9855
  · have he : independentCachedBranchMembers9879.filter (independentCachedEdge 1594)=independentCachedBranchMembers9878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9878
def independentCachedBranchMembers9880 : Finset ℕ := ([36,190,192,1582,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2740,2770,2776,3118,3126,3132,3162,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9880 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9880 5 (fun x => (if x<2620 then (if x<1716 then (if x<1582 then (if x<190 then 0 else (if x<192 then 0 else 1)) else (if x<1702 then 0 else (if x<1708 then 2 else 3))) else (if x<1752 then (if x<1738 then 0 else (if x<1746 then 1 else 2)) else (if x<2606 then 3 else (if x<2614 then 2 else 0)))) else (if x<3126 then (if x<2770 then (if x<2650 then 1 else (if x<2740 then 2 else 4)) else (if x<2776 then 3 else (if x<3118 then 1 else 3))) else (if x<3238 then (if x<3132 then 1 else (if x<3162 then 0 else 3)) else (if x<3244 then 0 else (if x<3274 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9881 : Finset ℕ := ([190,192,1716,1738,2614,2620,2740,3126,3132,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9881 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9881 4 (fun x => (if x<2620 then (if x<1716 then (if x<192 then 0 else 1) else (if x<1738 then 0 else (if x<2614 then 1 else 0))) else (if x<3126 then (if x<2740 then 1 else 2) else (if x<3132 then 1 else (if x<3274 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9882 : Finset ℕ := ([36,80,190,192,1582,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2740,2770,2776,3118,3126,3132,3162,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9882 80 4
  · have he : independentCachedBranchMembers9882.erase 80=independentCachedBranchMembers9880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9880
  · have he : independentCachedBranchMembers9882.filter (independentCachedEdge 80)=independentCachedBranchMembers9881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9881
def independentCachedBranchMembers9883 : Finset ℕ := ([190,1708,1716,1752,2620,2740,2776,3118,3126,3162,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9883 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9883 4 (fun x => (if x<2776 then (if x<1752 then (if x<1708 then 0 else (if x<1716 then 0 else 1)) else (if x<2620 then 1 else (if x<2740 then 0 else 2))) else (if x<3162 then (if x<3118 then 2 else (if x<3126 then 0 else 1)) else (if x<3238 then 1 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9884 : Finset ℕ := ([36,80,190,192,1582,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2740,2770,2776,3118,3126,3132,3162,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9884 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9884 3288 4
  · have he : independentCachedBranchMembers9884.erase 3288=independentCachedBranchMembers9882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9882
  · have he : independentCachedBranchMembers9884.filter (independentCachedEdge 3288)=independentCachedBranchMembers9883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9883
def independentCachedBranchMembers9885 : Finset ℕ := ([192,1702,1738,1746,2606,2614,2650,2740,2776,3132,3238,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9885 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9885 4 (fun x => (if x<2650 then (if x<1746 then (if x<1702 then 0 else (if x<1738 then 1 else 0)) else (if x<2606 then 1 else (if x<2614 then 1 else 0))) else (if x<3132 then (if x<2740 then 1 else (if x<2776 then 2 else 2)) else (if x<3238 then 0 else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9886 : Finset ℕ := ([36,80,190,192,1582,1702,1708,1716,1738,1746,1752,2606,2614,2620,2650,2726,2740,2770,2776,3118,3126,3132,3162,3238,3244,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9886 2726 4
  · have he : independentCachedBranchMembers9886.erase 2726=independentCachedBranchMembers9884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9884
  · have he : independentCachedBranchMembers9886.filter (independentCachedEdge 2726)=independentCachedBranchMembers9885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9885
def independentCachedBranchMembers9887 : Finset ℕ := ([80,1582,1702,1716,1738,1752,2614,2650,2770,3126,3162,3244] : List ℕ).toFinset
theorem independentCachedBranchBound9887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9887 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9887 4 (fun x => (if x<2614 then (if x<1716 then (if x<1582 then 0 else (if x<1702 then 0 else 1)) else (if x<1738 then 2 else (if x<1752 then 1 else 2))) else (if x<3126 then (if x<2650 then 1 else (if x<2770 then 1 else 0)) else (if x<3162 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
