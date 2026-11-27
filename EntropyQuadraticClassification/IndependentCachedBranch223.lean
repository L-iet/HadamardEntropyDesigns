/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch222
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers9920 : Finset ℕ := ([40,48,66,160,222,1614,1622,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2744,2758,2770,3132,3150,3158,3162,3244,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9920 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9920 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9920 40 4
  · have he : independentCachedBranchMembers9920.erase 40=independentCachedBranchMembers9918 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9918
  · have he : independentCachedBranchMembers9920.filter (independentCachedEdge 40)=independentCachedBranchMembers9919 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9919
def independentCachedBranchMembers9921 : Finset ℕ := ([48,160,1614,1716,1720,1746,2638,2740,2744,2770,3132,3158,3162,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9921 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9921 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9921 4 (fun x => (if x<2744 then (if x<1720 then (if x<1614 then (if x<160 then 0 else 1) else (if x<1716 then 0 else 1)) else (if x<2638 then (if x<1746 then 2 else 2) else (if x<2740 then 1 else 0))) else (if x<3162 then (if x<3132 then (if x<2770 then 3 else 3) else (if x<3158 then 2 else 2)) else (if x<3270 then (if x<3244 then 1 else 3) else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9922 : Finset ℕ := ([40,48,66,160,222,1614,1622,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2744,2758,2770,3132,3150,3158,3162,3244,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9922 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9922 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9922 3282 4
  · have he : independentCachedBranchMembers9922.erase 3282=independentCachedBranchMembers9920 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9920
  · have he : independentCachedBranchMembers9922.filter (independentCachedEdge 3282)=independentCachedBranchMembers9921 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9921
def independentCachedBranchMembers9923 : Finset ℕ := ([40,222,1622,1716,1734,1746,2646,2740,2758,2770,3132,3150,3162,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9923 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9923 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9923 4 (fun x => (if x<2758 then (if x<1734 then (if x<1622 then (if x<222 then 0 else 1) else (if x<1716 then 0 else 2)) else (if x<2646 then (if x<1746 then 1 else 2) else (if x<2740 then 1 else 3))) else (if x<3162 then (if x<3132 then (if x<2770 then 0 else 3) else (if x<3150 then 2 else 1)) else (if x<3256 then (if x<3244 then 2 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9924 : Finset ℕ := ([40,48,66,160,222,1614,1622,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2744,2758,2770,3132,3150,3158,3162,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9924 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9924 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9924 3252 4
  · have he : independentCachedBranchMembers9924.erase 3252=independentCachedBranchMembers9922 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9922
  · have he : independentCachedBranchMembers9924.filter (independentCachedEdge 3252)=independentCachedBranchMembers9923 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9923
def independentCachedBranchMembers9925 : Finset ℕ := ([40,160,1622,1708,1720,1738,2620,2638,2650,2740,2758,2770,3158,3244,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9925 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9925 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9925 4 (fun x => (if x<2650 then (if x<1720 then (if x<1622 then (if x<160 then 0 else 1) else (if x<1708 then 0 else 1)) else (if x<2620 then (if x<1738 then 2 else 2) else (if x<2638 then 2 else 2))) else (if x<3158 then (if x<2758 then (if x<2740 then 1 else 3) else (if x<2770 then 0 else 3)) else (if x<3256 then (if x<3244 then 1 else 3) else (if x<3274 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9926 : Finset ℕ := ([40,48,66,160,222,1614,1622,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2740,2744,2758,2762,2770,3132,3150,3158,3162,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9926 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9926 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9926 2762 4
  · have he : independentCachedBranchMembers9926.erase 2762=independentCachedBranchMembers9924 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9924
  · have he : independentCachedBranchMembers9926.filter (independentCachedEdge 2762)=independentCachedBranchMembers9925 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9925
def independentCachedBranchMembers9927 : Finset ℕ := ([48,222,1614,1708,1734,1738,2620,2646,2650,2740,2744,2770,3150,3244,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound9927 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9927 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9927 4 (fun x => (if x<2650 then (if x<1734 then (if x<1614 then (if x<222 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<2620 then (if x<1738 then 1 else 2) else (if x<2646 then 2 else 1))) else (if x<3150 then (if x<2744 then (if x<2740 then 2 else 0) else (if x<2770 then 3 else 3)) else (if x<3270 then (if x<3244 then 1 else 3) else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9928 : Finset ℕ := ([40,48,66,160,222,1614,1622,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2732,2740,2744,2758,2762,2770,3132,3150,3158,3162,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9928 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9928 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9928 2732 4
  · have he : independentCachedBranchMembers9928.erase 2732=independentCachedBranchMembers9926 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9926
  · have he : independentCachedBranchMembers9928.filter (independentCachedEdge 2732)=independentCachedBranchMembers9927 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9927
def independentCachedBranchMembers9929 : Finset ℕ := ([40,48,1614,1622,1708,1716,1738,1746,2620,2650,2744,2758,3132,3162,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound9929 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9929 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9929 4 (fun x => (if x<2620 then (if x<1708 then (if x<1614 then (if x<48 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1738 then (if x<1716 then 2 else 3) else (if x<1746 then 2 else 3))) else (if x<3132 then (if x<2744 then (if x<2650 then 2 else 2) else (if x<2758 then 0 else 1)) else (if x<3256 then (if x<3162 then 3 else 3) else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9930 : Finset ℕ := ([40,48,66,160,222,1614,1622,1626,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2732,2740,2744,2758,2762,2770,3132,3150,3158,3162,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9930 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9930 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9930 1626 4
  · have he : independentCachedBranchMembers9930.erase 1626=independentCachedBranchMembers9928 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9928
  · have he : independentCachedBranchMembers9930.filter (independentCachedEdge 1626)=independentCachedBranchMembers9929 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9929
def independentCachedBranchMembers9931 : Finset ℕ := ([160,222,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,3132,3150,3158,3162] : List ℕ).toFinset
theorem independentCachedBranchBound9931 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9931 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9931 4 (fun x => (if x<2620 then (if x<1720 then (if x<1708 then (if x<222 then 0 else 1) else (if x<1716 then 0 else 2)) else (if x<1738 then (if x<1734 then 3 else 1) else (if x<1746 then 3 else 2))) else (if x<3132 then (if x<2646 then (if x<2638 then 2 else 1) else (if x<2650 then 0 else 2)) else (if x<3158 then (if x<3150 then 3 else 3) else (if x<3162 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9932 : Finset ℕ := ([40,48,66,160,222,1596,1614,1622,1626,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2732,2740,2744,2758,2762,2770,3132,3150,3158,3162,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9932 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9932 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9932 1596 4
  · have he : independentCachedBranchMembers9932.erase 1596=independentCachedBranchMembers9930 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9930
  · have he : independentCachedBranchMembers9932.filter (independentCachedEdge 1596)=independentCachedBranchMembers9931 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9931
def independentCachedBranchMembers9933 : Finset ℕ := ([40,48,160,222,1614,1622,1720,1734,2638,2646,2744,2758,3150,3158,3256,3270] : List ℕ).toFinset
theorem independentCachedBranchBound9933 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9933 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9933 4 (fun x => (if x<2638 then (if x<1614 then (if x<160 then (if x<48 then 0 else 1) else (if x<222 then 2 else 3)) else (if x<1720 then (if x<1622 then 1 else 0) else (if x<1734 then 2 else 3))) else (if x<3150 then (if x<2744 then (if x<2646 then 2 else 3) else (if x<2758 then 0 else 1)) else (if x<3256 then (if x<3158 then 3 else 2) else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9934 : Finset ℕ := ([36,40,48,66,160,222,1596,1614,1622,1626,1708,1716,1720,1734,1738,1746,2620,2638,2646,2650,2732,2740,2744,2758,2762,2770,3132,3150,3158,3162,3244,3252,3256,3270,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9934 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9934 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9934 36 4
  · have he : independentCachedBranchMembers9934.erase 36=independentCachedBranchMembers9932 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9932
  · have he : independentCachedBranchMembers9934.filter (independentCachedEdge 36)=independentCachedBranchMembers9933 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9933
def independentCachedBranchMembers9935 : Finset ℕ := ([34,36,40,48,66,68,72,80,160,190,192,222,1582,1590,1594,1596,1614,1622,1626,1628,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,2606,2614,2618,2620,2638,2646,2650,2652,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9935 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9935 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9935 34 5
  · have he : independentCachedBranchMembers9935.erase 34=independentCachedBranchMembers9907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9907
  · have he : independentCachedBranchMembers9935.filter (independentCachedEdge 34)=independentCachedBranchMembers9934 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9934
def independentCachedBranchMembers9936 : Finset ℕ := ([10,12,18,20,34,36,40,48,66,68,72,80,96,126,130,132,136,144,160,190,192,222,238,246,250,252,1536,1566,1582,1590,1594,1596,1614,1622,1626,1628,1638,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9936 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9936 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9936 96 6
  · have he : independentCachedBranchMembers9936.erase 96=independentCachedBranchMembers9566 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9566
  · have he : independentCachedBranchMembers9936.filter (independentCachedEdge 96)=independentCachedBranchMembers9935 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9935
def independentCachedBranchMembers9937 : Finset ℕ := ([12,18,48,72,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2764,2800,3118,3158,3180,3186,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9937 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9937 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9937 6 (fun x => (if x<2666 then (if x<1686 then (if x<1590 then (if x<48 then (if x<18 then 0 else 0) else (if x<72 then 1 else 1)) else (if x<1644 then (if x<1614 then 1 else 1) else (if x<1650 then 0 else 0))) else (if x<1748 then (if x<1714 then (if x<1708 then 2 else 2) else (if x<1738 then 3 else 2)) else (if x<2614 then (if x<1776 then 3 else 2) else (if x<2638 then 4 else 4)))) else (if x<3158 then (if x<2738 then (if x<2710 then (if x<2676 then 5 else 5) else (if x<2732 then 3 else 0)) else (if x<2800 then (if x<2764 then 0 else 1) else (if x<3118 then 3 else 4))) else (if x<3250 then (if x<3186 then (if x<3180 then 4 else 5) else (if x<3214 then 5 else 2)) else (if x<3276 then (if x<3252 then 1 else 2) else (if x<3282 then 0 else (if x<3304 then 0 else 2)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9938 : Finset ℕ := ([12,72,1614,1644,1708,1738,2638,2666,2732,2764,3118,3180,3214,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9938 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9938 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9938 5 (fun x => (if x<2666 then (if x<1644 then (if x<72 then 0 else (if x<1614 then 1 else 0)) else (if x<1738 then (if x<1708 then 1 else 0) else (if x<2638 then 1 else 1))) else (if x<3180 then (if x<2764 then (if x<2732 then 2 else 2) else (if x<3118 then 0 else 2)) else (if x<3276 then (if x<3214 then 0 else 0) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9939 : Finset ℕ := ([12,18,48,72,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2764,2800,3118,3158,3180,3186,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9939 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9939 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9939 246 5
  · have he : independentCachedBranchMembers9939.erase 246=independentCachedBranchMembers9937 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9937
  · have he : independentCachedBranchMembers9939.filter (independentCachedEdge 246)=independentCachedBranchMembers9938 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9938
def independentCachedBranchMembers9940 : Finset ℕ := ([18,48,1590,1650,1708,1738,2614,2676,2732,2764,3158,3186,3214,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9940 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9940 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9940 5 (fun x => (if x<2676 then (if x<1650 then (if x<48 then 0 else (if x<1590 then 1 else 0)) else (if x<1738 then (if x<1708 then 1 else 0) else (if x<2614 then 1 else 1))) else (if x<3186 then (if x<2764 then (if x<2732 then 2 else 2) else (if x<3158 then 0 else 2)) else (if x<3276 then (if x<3214 then 0 else 2) else (if x<3304 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9941 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2764,2800,3118,3158,3180,3186,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9941 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9941 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9941 144 5
  · have he : independentCachedBranchMembers9941.erase 144=independentCachedBranchMembers9939 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9939
  · have he : independentCachedBranchMembers9941.filter (independentCachedEdge 144)=independentCachedBranchMembers9940 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9940
def independentCachedBranchMembers9942 : Finset ℕ := ([12,18,72,144,1614,1686,1708,1714,2638,2666,2676,2710,2732,2738,2764,3158,3180,3186,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9942 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9942 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9942 5 (fun x => (if x<2676 then (if x<1686 then (if x<72 then (if x<18 then 0 else 0) else (if x<144 then 1 else (if x<1614 then 1 else 1))) else (if x<1714 then (if x<1708 then 1 else 0) else (if x<2638 then 0 else (if x<2666 then 2 else 1)))) else (if x<3158 then (if x<2732 then (if x<2710 then 2 else 2) else (if x<2738 then 2 else (if x<2764 then 1 else 0))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3214 then 0 else (if x<3252 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9943 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2764,2800,3118,3158,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9943 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9943 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9943 3188 5
  · have he : independentCachedBranchMembers9943.erase 3188=independentCachedBranchMembers9941 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9941
  · have he : independentCachedBranchMembers9943.filter (independentCachedEdge 3188)=independentCachedBranchMembers9942 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9942
def independentCachedBranchMembers9944 : Finset ℕ := ([12,18,48,246,1590,1708,1714,1776,2614,2666,2676,2732,2738,2764,2800,3118,3180,3186,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9944 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9944 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9944 5 (fun x => (if x<2676 then (if x<1708 then (if x<48 then (if x<18 then 0 else 0) else (if x<246 then 1 else (if x<1590 then 1 else 1))) else (if x<1776 then (if x<1714 then 0 else 0) else (if x<2614 then 1 else (if x<2666 then 2 else 2)))) else (if x<3118 then (if x<2738 then (if x<2732 then 1 else 2) else (if x<2764 then 1 else (if x<2800 then 0 else 2))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3252 then 0 else (if x<3304 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9945 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2676,2710,2732,2738,2764,2800,3118,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9945 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9945 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9945 3178 5
  · have he : independentCachedBranchMembers9945.erase 3178=independentCachedBranchMembers9943 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9943
  · have he : independentCachedBranchMembers9945.filter (independentCachedEdge 3178)=independentCachedBranchMembers9944 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9944
def independentCachedBranchMembers9946 : Finset ℕ := ([72,144,1614,1644,1650,1686,1738,1748,2614,2666,2676,2732,2738,2764,2800,3118,3180,3186,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9946 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9946 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9946 5 (fun x => (if x<2676 then (if x<1686 then (if x<1614 then (if x<144 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1748 then (if x<1738 then 0 else 1) else (if x<2614 then 1 else (if x<2666 then 2 else 0)))) else (if x<3118 then (if x<2738 then (if x<2732 then 1 else 2) else (if x<2764 then 0 else (if x<2800 then 1 else 2))) else (if x<3186 then (if x<3180 then 2 else 0) else (if x<3252 then 2 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9947 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2674,2676,2710,2732,2738,2764,2800,3118,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9947 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9947 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9947 2674 5
  · have he : independentCachedBranchMembers9947.erase 2674=independentCachedBranchMembers9945 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9945
  · have he : independentCachedBranchMembers9947.filter (independentCachedEdge 2674)=independentCachedBranchMembers9946 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9946
def independentCachedBranchMembers9948 : Finset ℕ := ([48,246,1590,1644,1650,1738,1748,1776,2638,2666,2676,2710,2732,2738,2764,3158,3180,3186,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound9948 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9948 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9948 5 (fun x => (if x<2676 then (if x<1738 then (if x<1590 then (if x<246 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<1776 then (if x<1748 then 1 else 1) else (if x<2638 then 0 else (if x<2666 then 2 else 1)))) else (if x<3158 then (if x<2732 then (if x<2710 then 0 else 2) else (if x<2738 then 2 else (if x<2764 then 0 else 1))) else (if x<3186 then (if x<3180 then 2 else 2) else (if x<3214 then 0 else (if x<3252 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9949 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2668,2674,2676,2710,2732,2738,2764,2800,3118,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9949 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9949 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9949 2668 5
  · have he : independentCachedBranchMembers9949.erase 2668=independentCachedBranchMembers9947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9947
  · have he : independentCachedBranchMembers9949.filter (independentCachedEdge 2668)=independentCachedBranchMembers9948 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9948
def independentCachedBranchMembers9950 : Finset ℕ := ([18,246,1590,1614,1650,1686,1708,1748,2614,2638,2674,2676,2710,2732,3118,3158,3178,3180,3214,3250,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound9950 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9950 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9950 5 (fun x => (if x<2676 then (if x<1686 then (if x<1590 then (if x<246 then 0 else 0) else (if x<1614 then 0 else (if x<1650 then 1 else 1))) else (if x<2614 then (if x<1708 then 1 else (if x<1748 then 2 else 2)) else (if x<2638 then 3 else (if x<2674 then 3 else 0)))) else (if x<3178 then (if x<2732 then (if x<2710 then 4 else 0) else (if x<3118 then 3 else (if x<3158 then 2 else 0))) else (if x<3250 then (if x<3180 then 1 else (if x<3214 then 4 else 1)) else (if x<3252 then 0 else (if x<3276 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9951 : Finset ℕ := ([12,18,48,72,144,246,1590,1614,1644,1650,1686,1708,1714,1738,1748,1776,2614,2638,2666,2668,2674,2676,2710,2732,2738,2764,2800,3118,3150,3158,3178,3180,3186,3188,3214,3250,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9951 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9951 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9951 3150 5
  · have he : independentCachedBranchMembers9951.erase 3150=independentCachedBranchMembers9949 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9949
  · have he : independentCachedBranchMembers9951.filter (independentCachedEdge 3150)=independentCachedBranchMembers9950 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9950
end EntropyDesigns.QuadraticRefinement
