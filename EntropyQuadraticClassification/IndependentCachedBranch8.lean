/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch7
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1024 : Finset ℕ := ([72,132,1590,1642,1702,1734,1748,1768,2618,2650,2662,2710,2730,2762,2776,2788,3126,3158,3178,3192,3226,3238,3252,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1024 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1024 1590 4
  · have he : independentCachedBranchMembers1024.erase 1590=independentCachedBranchMembers1022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1022
  · have he : independentCachedBranchMembers1024.filter (independentCachedEdge 1590)=independentCachedBranchMembers1023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1023
def independentCachedBranchMembers1025 : Finset ℕ := ([72,132,1590,1594,1626,1642,1652,1686,1702,1720,1734,1738,1748,1752,1764,1768,2614,2618,2650,2662,2680,2710,2714,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3188,3192,3226,3238,3252,3256,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1025 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1025 2714 5
  · have he : independentCachedBranchMembers1025.erase 2714=independentCachedBranchMembers1019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1019
  · have he : independentCachedBranchMembers1025.filter (independentCachedEdge 2714)=independentCachedBranchMembers1024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1024
def independentCachedBranchMembers1026 : Finset ℕ := ([72,132,1642,1702,1752,1764,2614,2650,2662,2710,2730,2758,2772,2792,3130,3158,3178,3192,3226,3238,3252,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1026 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1026 5 (fun x => (if x<2772 then (if x<2614 then (if x<1702 then (if x<132 then 0 else (if x<1642 then 0 else 0)) else (if x<1752 then 0 else (if x<1764 then 1 else 1))) else (if x<2710 then (if x<2650 then 2 else (if x<2662 then 0 else 1)) else (if x<2730 then 0 else (if x<2758 then 2 else 2)))) else (if x<3226 then (if x<3158 then (if x<2792 then 1 else (if x<3130 then 1 else 2)) else (if x<3178 then 2 else (if x<3192 then 3 else 0))) else (if x<3274 then (if x<3238 then 3 else (if x<3252 then 2 else 0)) else (if x<3288 then 2 else (if x<3300 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1027 : Finset ℕ := ([132,1642,1752,2662,2710,2772,3130,3158,3192,3238,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1027 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1027 4 (fun x => (if x<3130 then (if x<2662 then (if x<1642 then 0 else (if x<1752 then 0 else 1)) else (if x<2710 then 1 else (if x<2772 then 0 else 1))) else (if x<3238 then (if x<3158 then 2 else (if x<3192 then 2 else 0)) else (if x<3274 then 2 else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1028 : Finset ℕ := ([72,132,1642,1702,1738,1752,1764,2614,2650,2662,2710,2730,2758,2772,2792,3130,3158,3178,3192,3226,3238,3252,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1028 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1028 1738 4
  · have he : independentCachedBranchMembers1028.erase 1738=independentCachedBranchMembers1026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1026
  · have he : independentCachedBranchMembers1028.filter (independentCachedEdge 1738)=independentCachedBranchMembers1027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1027
def independentCachedBranchMembers1029 : Finset ℕ := ([72,1642,1764,2662,2710,2792,3130,3158,3238,3252,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1029 4 (fun x => (if x<3130 then (if x<2662 then (if x<1642 then 0 else (if x<1764 then 0 else 1)) else (if x<2710 then 1 else (if x<2792 then 0 else 1))) else (if x<3252 then (if x<3158 then 2 else (if x<3238 then 2 else 2)) else (if x<3274 then 0 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1030 : Finset ℕ := ([72,132,1594,1642,1702,1738,1752,1764,2614,2650,2662,2710,2730,2758,2772,2792,3130,3158,3178,3192,3226,3238,3252,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1030 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1030 1594 4
  · have he : independentCachedBranchMembers1030.erase 1594=independentCachedBranchMembers1028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1028
  · have he : independentCachedBranchMembers1030.filter (independentCachedEdge 1594)=independentCachedBranchMembers1029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1029
def independentCachedBranchMembers1031 : Finset ℕ := ([72,132,1590,1594,1626,1642,1652,1686,1702,1720,1734,1738,1748,1752,1764,1768,2614,2618,2646,2650,2662,2680,2710,2714,2730,2740,2758,2762,2772,2776,2788,2792,3126,3130,3158,3178,3188,3192,3226,3238,3252,3256,3270,3274,3284,3288,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1031 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1031 2646 5
  · have he : independentCachedBranchMembers1031.erase 2646=independentCachedBranchMembers1025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1025
  · have he : independentCachedBranchMembers1031.filter (independentCachedEdge 2646)=independentCachedBranchMembers1030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1030
def independentCachedBranchMembers1032 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1032 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1032 12 6
  · have he : independentCachedBranchMembers1032.erase 12=independentCachedBranchMembers978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound978
  · have he : independentCachedBranchMembers1032.filter (independentCachedEdge 12)=independentCachedBranchMembers1031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1031
def independentCachedBranchMembers1033 : Finset ℕ := ([132,252,1642,1652,1702,1720,1740,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1033 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1033 6 (fun x => (if x<2762 then (if x<2620 then (if x<1652 then (if x<252 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then (if x<1702 then 1 else 1) else (if x<1740 then 1 else 0))) else (if x<2710 then (if x<2668 then (if x<2650 then 2 else 2) else (if x<2674 then 3 else 3)) else (if x<2738 then (if x<2732 then 2 else 0) else (if x<2758 then 4 else 3)))) else (if x<3164 then (if x<2800 then (if x<2772 then 4 else (if x<2776 then 0 else 3)) else (if x<3130 then (if x<3126 then 2 else 4) else (if x<3150 then 5 else 4))) else (if x<3252 then (if x<3214 then (if x<3192 then 5 else 1) else (if x<3228 then 5 else 0)) else (if x<3300 then (if x<3282 then 1 else 2) else (if x<3304 then 0 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1034 : Finset ℕ := ([1652,1720,2620,2674,2732,2758,2772,2800,3130,3214,3228,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1034 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1034 5 (fun x => (if x<2772 then (if x<2674 then (if x<1720 then 0 else (if x<2620 then 0 else 0)) else (if x<2732 then 1 else (if x<2758 then 2 else 1))) else (if x<3214 then (if x<2800 then 2 else (if x<3130 then 0 else 1)) else (if x<3282 then (if x<3228 then 1 else 2) else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1035 : Finset ℕ := ([72,132,252,1642,1652,1702,1720,1740,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1035 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1035 72 5
  · have he : independentCachedBranchMembers1035.erase 72=independentCachedBranchMembers1033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1033
  · have he : independentCachedBranchMembers1035.filter (independentCachedEdge 72)=independentCachedBranchMembers1034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1034
def independentCachedBranchMembers1036 : Finset ℕ := ([1642,1702,2650,2668,2710,2732,2772,2776,3164,3228,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1036 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1036 5 (fun x => (if x<2772 then (if x<2668 then (if x<1702 then 0 else (if x<2650 then 0 else 0)) else (if x<2710 then 1 else (if x<2732 then 0 else 2))) else (if x<3228 then (if x<2776 then 1 else (if x<3164 then 2 else 1)) else (if x<3300 then (if x<3282 then 2 else 1) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1037 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,1740,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1037 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1037 48 5
  · have he : independentCachedBranchMembers1037.erase 48=independentCachedBranchMembers1035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1035
  · have he : independentCachedBranchMembers1037.filter (independentCachedEdge 48)=independentCachedBranchMembers1036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1036
def independentCachedBranchMembers1038 : Finset ℕ := ([48,72,132,252,3126,3130,3150,3164,3192,3214,3228,3252,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1038 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1038 5 (fun x => (if x<3164 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<3130 then (if x<3126 then 0 else 1) else (if x<3150 then 2 else 1))) else (if x<3252 then (if x<3214 then (if x<3192 then 2 else 0) else (if x<3228 then 2 else 1)) else (if x<3300 then (if x<3282 then 0 else 1) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1039 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,1740,1746,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1039 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1039 1746 5
  · have he : independentCachedBranchMembers1039.erase 1746=independentCachedBranchMembers1037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1037
  · have he : independentCachedBranchMembers1039.filter (independentCachedEdge 1746)=independentCachedBranchMembers1038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1038
def independentCachedBranchMembers1040 : Finset ℕ := ([1642,1652,1702,1720,1740,1746,2620,2650,2710,2800,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1040 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1040 5 (fun x => (if x<2800 then (if x<1740 then (if x<1702 then (if x<1652 then 0 else 0) else (if x<1720 then 0 else 0)) else (if x<2620 then (if x<1746 then 0 else 0) else (if x<2650 then 1 else (if x<2710 then 1 else 1)))) else (if x<3164 then (if x<3130 then (if x<3126 then 1 else 2) else (if x<3150 then 3 else 2)) else (if x<3228 then (if x<3214 then 3 else 3) else (if x<3300 then 2 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1041 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,1740,1746,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1041 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1041 3276 5
  · have he : independentCachedBranchMembers1041.erase 3276=independentCachedBranchMembers1039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1039
  · have he : independentCachedBranchMembers1041.filter (independentCachedEdge 3276)=independentCachedBranchMembers1040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1040
def independentCachedBranchMembers1042 : Finset ℕ := ([48,132,1642,1720,1740,2620,2650,2674,2738,2758,2772,3130,3150,3164,3214,3228,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1042 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1042 5 (fun x => (if x<2758 then (if x<1740 then (if x<1642 then (if x<132 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<2650 then (if x<2620 then 0 else 2) else (if x<2674 then 2 else (if x<2738 then 0 else 2)))) else (if x<3214 then (if x<3130 then (if x<2772 then 0 else 2) else (if x<3150 then 0 else (if x<3164 then 1 else 2))) else (if x<3252 then (if x<3228 then 0 else 1) else (if x<3282 then 2 else (if x<3304 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1043 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,1740,1746,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1043 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1043 1768 5
  · have he : independentCachedBranchMembers1043.erase 1768=independentCachedBranchMembers1041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1041
  · have he : independentCachedBranchMembers1043.filter (independentCachedEdge 1768)=independentCachedBranchMembers1042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1042
def independentCachedBranchMembers1044 : Finset ℕ := ([72,252,1652,1702,1740,2620,2650,2668,2738,2772,2776,3126,3130,3164,3214,3252,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1044 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1044 5 (fun x => (if x<2772 then (if x<1740 then (if x<1652 then (if x<252 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2650 then (if x<2620 then 0 else 2) else (if x<2668 then 2 else (if x<2738 then 0 else 2)))) else (if x<3214 then (if x<3126 then (if x<2776 then 2 else 0) else (if x<3130 then 1 else (if x<3164 then 2 else 0))) else (if x<3282 then (if x<3252 then 1 else 2) else (if x<3300 then 2 else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1045 : Finset ℕ := ([48,72,132,252,1642,1652,1678,1702,1720,1740,1746,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1045 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1045 1678 5
  · have he : independentCachedBranchMembers1045.erase 1678=independentCachedBranchMembers1043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1043
  · have he : independentCachedBranchMembers1045.filter (independentCachedEdge 1678)=independentCachedBranchMembers1044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1044
def independentCachedBranchMembers1046 : Finset ℕ := ([48,132,1652,1702,1740,2674,2710,2732,2758,2762,2800,3126,3130,3164,3214,3252,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1046 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1046 5 (fun x => (if x<2762 then (if x<1740 then (if x<1652 then (if x<132 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<2710 then (if x<2674 then 0 else 0) else (if x<2732 then 2 else (if x<2758 then 2 else 0)))) else (if x<3214 then (if x<3126 then (if x<2800 then 2 else 2) else (if x<3130 then 1 else (if x<3164 then 0 else 1))) else (if x<3282 then (if x<3252 then 0 else 2) else (if x<3300 then 2 else (if x<3304 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1047 : Finset ℕ := ([48,72,132,252,1628,1642,1652,1678,1702,1720,1740,1746,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1047 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1047 1628 5
  · have he : independentCachedBranchMembers1047.erase 1628=independentCachedBranchMembers1045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1045
  · have he : independentCachedBranchMembers1047.filter (independentCachedEdge 1628)=independentCachedBranchMembers1046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1046
def independentCachedBranchMembers1048 : Finset ℕ := ([72,252,1642,1720,1740,2668,2710,2732,2762,2776,2800,3130,3150,3164,3214,3228,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1048 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1048 5 (fun x => (if x<2776 then (if x<1740 then (if x<1642 then (if x<252 then 0 else 0) else (if x<1720 then 1 else 1)) else (if x<2710 then (if x<2668 then 0 else 0) else (if x<2732 then 2 else (if x<2762 then 2 else 2)))) else (if x<3214 then (if x<3130 then (if x<2800 then 0 else 2) else (if x<3150 then 1 else (if x<3164 then 1 else 0))) else (if x<3252 then (if x<3228 then 2 else 1) else (if x<3282 then 2 else (if x<3304 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1049 : Finset ℕ := ([48,72,132,252,1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1049 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1049 1594 5
  · have he : independentCachedBranchMembers1049.erase 1594=independentCachedBranchMembers1047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1047
  · have he : independentCachedBranchMembers1049.filter (independentCachedEdge 1594)=independentCachedBranchMembers1048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1048
def independentCachedBranchMembers1050 : Finset ℕ := ([48,72,1594,1652,1702,1740,1768,2620,2674,2710,2738,2762,2776,3126,3150,3164,3192,3214,3228,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1050 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1050 5 (fun x => (if x<2738 then (if x<1740 then (if x<1594 then (if x<72 then 0 else 0) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<2620 then (if x<1768 then 0 else 1) else (if x<2674 then 2 else (if x<2710 then 2 else 2)))) else (if x<3164 then (if x<2776 then (if x<2762 then 0 else 0) else (if x<3126 then 2 else (if x<3150 then 0 else 0))) else (if x<3228 then (if x<3192 then 3 else (if x<3214 then 1 else 3)) else (if x<3282 then 2 else (if x<3300 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1051 : Finset ℕ := ([48,72,132,252,1594,1628,1642,1652,1678,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1051 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1051 1764 5
  · have he : independentCachedBranchMembers1051.erase 1764=independentCachedBranchMembers1049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1049
  · have he : independentCachedBranchMembers1051.filter (independentCachedEdge 1764)=independentCachedBranchMembers1050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1050
def independentCachedBranchMembers1052 : Finset ℕ := ([48,72,1628,1642,1678,1720,1740,2650,2668,2738,2758,2762,2800,3126,3130,3150,3192,3228,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1052 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1052 5 (fun x => (if x<2758 then (if x<1720 then (if x<1628 then (if x<72 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 1 else 1))) else (if x<2650 then (if x<1740 then 1 else 0) else (if x<2668 then 2 else (if x<2738 then 2 else 0)))) else (if x<3150 then (if x<2800 then (if x<2762 then 2 else 0) else (if x<3126 then 2 else (if x<3130 then 0 else 3))) else (if x<3282 then (if x<3192 then 0 else (if x<3228 then 1 else 1)) else (if x<3300 then 2 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1053 : Finset ℕ := ([48,72,132,252,1594,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1053 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1053 1692 5
  · have he : independentCachedBranchMembers1053.erase 1692=independentCachedBranchMembers1051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1051
  · have he : independentCachedBranchMembers1053.filter (independentCachedEdge 1692)=independentCachedBranchMembers1052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1052
def independentCachedBranchMembers1054 : Finset ℕ := ([132,252,1628,1642,1678,1720,1740,2620,2674,2710,2732,2772,2776,3126,3130,3150,3192,3228,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1054 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1054 5 (fun x => (if x<2732 then (if x<1720 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1642 then 1 else (if x<1678 then 1 else 1))) else (if x<2620 then (if x<1740 then 1 else 0) else (if x<2674 then 2 else (if x<2710 then 2 else 2)))) else (if x<3150 then (if x<2776 then (if x<2772 then 0 else 0) else (if x<3126 then 2 else (if x<3130 then 2 else 3))) else (if x<3282 then (if x<3192 then 1 else (if x<3228 then 1 else 0)) else (if x<3300 then 2 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1055 : Finset ℕ := ([48,72,132,252,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1055 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1055 1614 5
  · have he : independentCachedBranchMembers1055.erase 1614=independentCachedBranchMembers1053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1053
  · have he : independentCachedBranchMembers1055.filter (independentCachedEdge 1614)=independentCachedBranchMembers1054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1054
def independentCachedBranchMembers1056 : Finset ℕ := ([132,252,1594,1652,1702,1740,1768,2650,2668,2732,2758,2772,2800,3126,3150,3164,3192,3214,3228,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1056 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1056 5 (fun x => (if x<2758 then (if x<1740 then (if x<1594 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<2650 then (if x<1768 then 0 else 1) else (if x<2668 then 2 else (if x<2732 then 2 else 0)))) else (if x<3164 then (if x<2800 then (if x<2772 then 2 else 0) else (if x<3126 then 2 else (if x<3150 then 1 else 2))) else (if x<3228 then (if x<3192 then 3 else (if x<3214 then 1 else 3)) else (if x<3282 then 0 else (if x<3300 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1057 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1057 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1057 1590 5
  · have he : independentCachedBranchMembers1057.erase 1590=independentCachedBranchMembers1055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1055
  · have he : independentCachedBranchMembers1057.filter (independentCachedEdge 1590)=independentCachedBranchMembers1056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1056
def independentCachedBranchMembers1058 : Finset ℕ := ([72,132,1590,1628,1642,1652,1678,1702,1720,1740,1746,1764,2650,2668,2674,2710,2762,2772,3130,3150,3192,3228,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1058 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1058 5 (fun x => (if x<2650 then (if x<1678 then (if x<1628 then (if x<132 then 0 else (if x<1590 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 0 else 2))) else (if x<1740 then (if x<1702 then 1 else (if x<1720 then 0 else 1)) else (if x<1746 then 0 else (if x<1764 then 1 else 1)))) else (if x<3130 then (if x<2710 then (if x<2668 then 3 else (if x<2674 then 2 else 2)) else (if x<2762 then 3 else (if x<2772 then 2 else 2))) else (if x<3228 then (if x<3150 then 4 else (if x<3192 then 4 else 3)) else (if x<3252 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1059 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1059 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1059 3256 5
  · have he : independentCachedBranchMembers1059.erase 3256=independentCachedBranchMembers1057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1057
  · have he : independentCachedBranchMembers1059.filter (independentCachedEdge 3256)=independentCachedBranchMembers1058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1058
def independentCachedBranchMembers1060 : Finset ℕ := ([48,252,1594,1614,1642,1652,1692,1702,1720,1740,1746,1768,2620,2668,2674,2762,2772,2800,3126,3164,3192,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1060 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1060 5 (fun x => (if x<2620 then (if x<1692 then (if x<1614 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 2 else 0))) else (if x<1740 then (if x<1702 then 1 else (if x<1720 then 1 else 0)) else (if x<1746 then 0 else (if x<1768 then 1 else 1)))) else (if x<3126 then (if x<2762 then (if x<2668 then 3 else (if x<2674 then 2 else 2)) else (if x<2772 then 2 else (if x<2800 then 2 else 3))) else (if x<3214 then (if x<3164 then 4 else (if x<3192 then 4 else 3)) else (if x<3252 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1061 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1061 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1061 3238 5
  · have he : independentCachedBranchMembers1061.erase 3238=independentCachedBranchMembers1059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1059
  · have he : independentCachedBranchMembers1061.filter (independentCachedEdge 3238)=independentCachedBranchMembers1060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1060
def independentCachedBranchMembers1062 : Finset ℕ := ([72,132,1594,1614,1642,1652,1692,1702,1720,1740,1746,1768,2650,2710,2732,2738,2758,2776,3126,3164,3192,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1062 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1062 5 (fun x => (if x<2650 then (if x<1692 then (if x<1614 then (if x<132 then 0 else (if x<1594 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 0 else 1))) else (if x<1740 then (if x<1702 then 1 else (if x<1720 then 0 else 2)) else (if x<1746 then 0 else (if x<1768 then 1 else 1)))) else (if x<3126 then (if x<2738 then (if x<2710 then 3 else (if x<2732 then 3 else 2)) else (if x<2758 then 2 else (if x<2776 then 2 else 2))) else (if x<3214 then (if x<3164 then 4 else (if x<3192 then 4 else 3)) else (if x<3252 then 4 else (if x<3300 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1063 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1063 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1063 3188 5
  · have he : independentCachedBranchMembers1063.erase 3188=independentCachedBranchMembers1061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1061
  · have he : independentCachedBranchMembers1063.filter (independentCachedEdge 3188)=independentCachedBranchMembers1062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1062
def independentCachedBranchMembers1064 : Finset ℕ := ([48,252,1590,1628,1642,1652,1678,1702,1720,1740,1746,1764,2620,2732,2738,2758,2776,2800,3130,3150,3192,3228,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1064 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1064 5 (fun x => (if x<2620 then (if x<1678 then (if x<1628 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 1 else 0))) else (if x<1740 then (if x<1702 then 1 else (if x<1720 then 2 else 0)) else (if x<1746 then 0 else (if x<1764 then 1 else 1)))) else (if x<3130 then (if x<2758 then (if x<2732 then 3 else (if x<2738 then 2 else 2)) else (if x<2776 then 2 else (if x<2800 then 2 else 3))) else (if x<3228 then (if x<3150 then 4 else (if x<3192 then 4 else 3)) else (if x<3252 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1065 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1065 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1065 3178 5
  · have he : independentCachedBranchMembers1065.erase 3178=independentCachedBranchMembers1063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1063
  · have he : independentCachedBranchMembers1065.filter (independentCachedEdge 3178)=independentCachedBranchMembers1064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1064
def independentCachedBranchMembers1066 : Finset ℕ := ([132,252,1642,1652,1702,1720,1740,2668,2674,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1066 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1066 5 (fun x => (if x<2758 then (if x<1720 then (if x<1642 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<2674 then (if x<1740 then 1 else (if x<2668 then 0 else 2)) else (if x<2732 then 2 else (if x<2738 then 0 else 3)))) else (if x<3150 then (if x<2776 then (if x<2762 then 2 else (if x<2772 then 3 else 0)) else (if x<3126 then 2 else (if x<3130 then 3 else 4))) else (if x<3228 then (if x<3164 then 3 else (if x<3214 then 4 else 4)) else (if x<3300 then 0 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1067 : Finset ℕ := ([1652,1720,2674,2732,2758,2772,3130,3214,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1067 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1067 4 (fun x => (if x<2772 then (if x<2674 then (if x<1720 then 0 else 0) else (if x<2732 then 1 else (if x<2758 then 2 else 1))) else (if x<3214 then (if x<3130 then 2 else 1) else (if x<3228 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1068 : Finset ℕ := ([72,132,252,1642,1652,1702,1720,1740,2668,2674,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1068 72 4
  · have he : independentCachedBranchMembers1068.erase 72=independentCachedBranchMembers1066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1066
  · have he : independentCachedBranchMembers1068.filter (independentCachedEdge 72)=independentCachedBranchMembers1067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1067
def independentCachedBranchMembers1069 : Finset ℕ := ([1642,1702,2668,2732,2772,2776,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1069 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1069 4 (fun x => (if x<2776 then (if x<2668 then (if x<1702 then 0 else 0) else (if x<2732 then 1 else (if x<2772 then 2 else 1))) else (if x<3228 then (if x<3164 then 2 else 1) else (if x<3300 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1070 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,1740,2668,2674,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1070 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1070 48 4
  · have he : independentCachedBranchMembers1070.erase 48=independentCachedBranchMembers1068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1068
  · have he : independentCachedBranchMembers1070.filter (independentCachedEdge 48)=independentCachedBranchMembers1069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1069
def independentCachedBranchMembers1071 : Finset ℕ := ([48,72,132,252,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1071 4 (fun x => (if x<3150 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<3126 then 0 else (if x<3130 then 1 else 2))) else (if x<3228 then (if x<3164 then 1 else (if x<3214 then 2 else 2)) else (if x<3300 then 1 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1072 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,1740,1746,2668,2674,2732,2738,2758,2762,2772,2776,3126,3130,3150,3164,3214,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1072 1746 4
  · have he : independentCachedBranchMembers1072.erase 1746=independentCachedBranchMembers1070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1070
  · have he : independentCachedBranchMembers1072.filter (independentCachedEdge 1746)=independentCachedBranchMembers1071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1071
def independentCachedBranchMembers1073 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2800,3102,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1073 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1073 3102 5
  · have he : independentCachedBranchMembers1073.erase 3102=independentCachedBranchMembers1065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1065
  · have he : independentCachedBranchMembers1073.filter (independentCachedEdge 3102)=independentCachedBranchMembers1072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1072
def independentCachedBranchMembers1074 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1652,1678,1720,1740,2620,2674,2738,2758,2762,2800,3126,3130,3150,3192,3214,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1074 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1074 5 (fun x => (if x<2674 then (if x<1614 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1590 then 0 else (if x<1594 then 1 else 2))) else (if x<1720 then (if x<1652 then 1 else (if x<1678 then 2 else 3)) else (if x<1740 then 3 else (if x<2620 then 0 else 2)))) else (if x<3130 then (if x<2762 then (if x<2738 then 2 else (if x<2758 then 1 else 3)) else (if x<2800 then 1 else (if x<3126 then 3 else 2))) else (if x<3214 then (if x<3150 then 4 else (if x<3192 then 3 else 2)) else (if x<3252 then 4 else (if x<3276 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1075 : Finset ℕ := ([132,1590,1678,1720,1740,2674,2762,3130,3150,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1075 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1075 4 (fun x => (if x<2674 then (if x<1678 then (if x<1590 then 0 else 1) else (if x<1720 then 0 else (if x<1740 then 1 else 2))) else (if x<3150 then (if x<2762 then 0 else (if x<3130 then 2 else 1)) else (if x<3192 then 2 else (if x<3252 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1076 : Finset ℕ := ([1678,1720,2674,3130] : List ℕ).toFinset
theorem independentCachedBranchBound1076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1076 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1076 3 (fun x => (if x<2674 then (if x<1720 then 0 else 0) else (if x<3130 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1077 : Finset ℕ := ([72,132,1590,1678,1720,1740,2674,2762,3130,3150,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1077 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1077 72 3
  · have he : independentCachedBranchMembers1077.erase 72=independentCachedBranchMembers1075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1075
  · have he : independentCachedBranchMembers1077.filter (independentCachedEdge 72)=independentCachedBranchMembers1076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1076
def independentCachedBranchMembers1078 : Finset ℕ := ([72,132,1590,1678,3130,3150] : List ℕ).toFinset
theorem independentCachedBranchBound1078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1078 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1078 3 (fun x => (if x<1678 then (if x<132 then 0 else (if x<1590 then 0 else 1)) else (if x<3130 then 1 else (if x<3150 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1079 : Finset ℕ := ([72,132,1590,1652,1678,1720,1740,2674,2762,3130,3150,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1079 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1079 1652 3
  · have he : independentCachedBranchMembers1079.erase 1652=independentCachedBranchMembers1077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1077
  · have he : independentCachedBranchMembers1079.filter (independentCachedEdge 1652)=independentCachedBranchMembers1078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1078
def independentCachedBranchMembers1080 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1652,1678,1720,1740,2620,2674,2738,2758,2762,2800,3126,3130,3150,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1080 3256 4
  · have he : independentCachedBranchMembers1080.erase 3256=independentCachedBranchMembers1074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1074
  · have he : independentCachedBranchMembers1080.filter (independentCachedEdge 3256)=independentCachedBranchMembers1079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1079
def independentCachedBranchMembers1081 : Finset ℕ := ([132,1594,1614,1652,1740,2738,2758,3126,3192,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1081 4 (fun x => (if x<2738 then (if x<1614 then (if x<1594 then 0 else 0) else (if x<1652 then 1 else (if x<1740 then 1 else 2))) else (if x<3192 then (if x<2758 then 2 else (if x<3126 then 0 else 2)) else (if x<3214 then 0 else (if x<3252 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1082 : Finset ℕ := ([1594,1652,2758,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1082 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1082 3 (fun x => (if x<2758 then (if x<1652 then 0 else 0) else (if x<3214 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1083 : Finset ℕ := ([72,132,1594,1614,1652,1740,2738,2758,3126,3192,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1083 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1083 72 3
  · have he : independentCachedBranchMembers1083.erase 72=independentCachedBranchMembers1081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1081
  · have he : independentCachedBranchMembers1083.filter (independentCachedEdge 72)=independentCachedBranchMembers1082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1082
def independentCachedBranchMembers1084 : Finset ℕ := ([72,132,1594,1614,3126,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1084 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1084 3 (fun x => (if x<1614 then (if x<132 then 0 else (if x<1594 then 0 else 1)) else (if x<3126 then 1 else (if x<3214 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1085 : Finset ℕ := ([72,132,1594,1614,1652,1720,1740,2738,2758,3126,3192,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1085 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1085 1720 3
  · have he : independentCachedBranchMembers1085.erase 1720=independentCachedBranchMembers1083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1083
  · have he : independentCachedBranchMembers1085.filter (independentCachedEdge 1720)=independentCachedBranchMembers1084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1084
def independentCachedBranchMembers1086 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1652,1678,1720,1740,2620,2674,2738,2758,2762,2800,3126,3130,3150,3188,3192,3214,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound1086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1086 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1086 3188 4
  · have he : independentCachedBranchMembers1086.erase 3188=independentCachedBranchMembers1080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1080
  · have he : independentCachedBranchMembers1086.filter (independentCachedEdge 3188)=independentCachedBranchMembers1085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1085
def independentCachedBranchMembers1087 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2732,2738,2758,2762,2772,2776,2786,2800,3102,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1087 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1087 2786 5
  · have he : independentCachedBranchMembers1087.erase 2786=independentCachedBranchMembers1073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1073
  · have he : independentCachedBranchMembers1087.filter (independentCachedEdge 2786)=independentCachedBranchMembers1086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1086
def independentCachedBranchMembers1088 : Finset ℕ := ([48,72,132,252,1590,1614,1628,1642,1702,1740,1768,2650,2668,2710,2738,2762,2776,3126,3150,3164,3192,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1088 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1088 5 (fun x => (if x<2668 then (if x<1628 then (if x<252 then (if x<72 then 0 else (if x<132 then 0 else 0)) else (if x<1590 then 0 else (if x<1614 then 1 else 1))) else (if x<1740 then (if x<1642 then 2 else (if x<1702 then 2 else 3)) else (if x<1768 then 0 else (if x<2650 then 3 else 2)))) else (if x<3150 then (if x<2762 then (if x<2710 then 2 else (if x<2738 then 3 else 1)) else (if x<2776 then 1 else (if x<3126 then 3 else 3))) else (if x<3252 then (if x<3164 then 2 else (if x<3192 then 4 else 2)) else (if x<3276 then 1 else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1089 : Finset ℕ := ([252,1614,1702,1740,1768,2668,2762,3126,3164,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1089 4 (fun x => (if x<2668 then (if x<1702 then (if x<1614 then 0 else 1) else (if x<1740 then 1 else (if x<1768 then 0 else 1))) else (if x<3164 then (if x<2762 then 0 else (if x<3126 then 2 else 2)) else (if x<3192 then 0 else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1090 : Finset ℕ := ([1702,1768,2668,3164] : List ℕ).toFinset
theorem independentCachedBranchBound1090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1090 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1090 3 (fun x => (if x<2668 then (if x<1768 then 0 else 0) else (if x<3164 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1091 : Finset ℕ := ([48,252,1614,1702,1740,1768,2668,2762,3126,3164,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1091 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1091 48 3
  · have he : independentCachedBranchMembers1091.erase 48=independentCachedBranchMembers1089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1089
  · have he : independentCachedBranchMembers1091.filter (independentCachedEdge 48)=independentCachedBranchMembers1090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1090
def independentCachedBranchMembers1092 : Finset ℕ := ([48,252,1614,1768,3126,3164] : List ℕ).toFinset
theorem independentCachedBranchBound1092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1092 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1092 3 (fun x => (if x<1768 then (if x<252 then 0 else (if x<1614 then 0 else 1)) else (if x<3126 then 1 else (if x<3164 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1093 : Finset ℕ := ([48,252,1614,1642,1702,1740,1768,2668,2762,3126,3164,3192,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1093 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1093 1642 3
  · have he : independentCachedBranchMembers1093.erase 1642=independentCachedBranchMembers1091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1091
  · have he : independentCachedBranchMembers1093.filter (independentCachedEdge 1642)=independentCachedBranchMembers1092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1092
def independentCachedBranchMembers1094 : Finset ℕ := ([48,72,132,252,1590,1614,1628,1642,1702,1740,1768,2650,2668,2710,2738,2762,2776,3126,3150,3164,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1094 3238 4
  · have he : independentCachedBranchMembers1094.erase 3238=independentCachedBranchMembers1088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1088
  · have he : independentCachedBranchMembers1094.filter (independentCachedEdge 3238)=independentCachedBranchMembers1093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1093
def independentCachedBranchMembers1095 : Finset ℕ := ([252,1590,1628,1642,1740,2738,2776,3150,3192,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1095 4 (fun x => (if x<2738 then (if x<1628 then (if x<1590 then 0 else 1) else (if x<1642 then 0 else (if x<1740 then 1 else 2))) else (if x<3192 then (if x<2776 then 2 else (if x<3150 then 0 else 2)) else (if x<3252 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1096 : Finset ℕ := ([1628,1642,2776,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1096 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1096 3 (fun x => (if x<2776 then (if x<1642 then 0 else 0) else (if x<3304 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1097 : Finset ℕ := ([48,252,1590,1628,1642,1740,2738,2776,3150,3192,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1097 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1097 48 3
  · have he : independentCachedBranchMembers1097.erase 48=independentCachedBranchMembers1095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1095
  · have he : independentCachedBranchMembers1097.filter (independentCachedEdge 48)=independentCachedBranchMembers1096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1096
def independentCachedBranchMembers1098 : Finset ℕ := ([48,252,1590,1628,3150,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1098 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1098 3 (fun x => (if x<1628 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<3150 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1099 : Finset ℕ := ([48,252,1590,1628,1642,1702,1740,2738,2776,3150,3192,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1099 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1099 1702 3
  · have he : independentCachedBranchMembers1099.erase 1702=independentCachedBranchMembers1097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1097
  · have he : independentCachedBranchMembers1099.filter (independentCachedEdge 1702)=independentCachedBranchMembers1098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1098
def independentCachedBranchMembers1100 : Finset ℕ := ([48,72,132,252,1590,1614,1628,1642,1702,1740,1768,2650,2668,2710,2738,2762,2776,3126,3150,3164,3178,3192,3238,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1100 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1100 3178 4
  · have he : independentCachedBranchMembers1100.erase 3178=independentCachedBranchMembers1094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1094
  · have he : independentCachedBranchMembers1100.filter (independentCachedEdge 3178)=independentCachedBranchMembers1099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1099
def independentCachedBranchMembers1101 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800,3102,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1101 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1101 2714 5
  · have he : independentCachedBranchMembers1101.erase 2714=independentCachedBranchMembers1087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1087
  · have he : independentCachedBranchMembers1101.filter (independentCachedEdge 2714)=independentCachedBranchMembers1100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1100
def independentCachedBranchMembers1102 : Finset ℕ := ([132,1642,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3192,3214,3228,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1102 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1102 5 (fun x => (if x<2732 then (if x<1740 then (if x<1692 then (if x<1642 then 0 else 0) else (if x<1702 then 1 else 0)) else (if x<2650 then (if x<1764 then 0 else 1) else (if x<2674 then 2 else (if x<2710 then 3 else 2)))) else (if x<3214 then (if x<2772 then (if x<2758 then 1 else 3) else (if x<3130 then 1 else (if x<3192 then 3 else 2))) else (if x<3252 then (if x<3228 then 3 else 4) else (if x<3276 then 1 else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1103 : Finset ℕ := ([1692,1702,1740,2650,2772,3130,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1103 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1103 4 (fun x => (if x<2772 then (if x<1740 then (if x<1702 then 0 else 0) else (if x<2650 then 1 else 2)) else (if x<3214 then (if x<3130 then 1 else 1) else (if x<3252 then 0 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1104 : Finset ℕ := ([132,1642,1678,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3192,3214,3228,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1104 1678 4
  · have he : independentCachedBranchMembers1104.erase 1678=independentCachedBranchMembers1102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1102
  · have he : independentCachedBranchMembers1104.filter (independentCachedEdge 1678)=independentCachedBranchMembers1103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1103
def independentCachedBranchMembers1105 : Finset ℕ := ([1642,1740,1764,2710,2732,3130,3214,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1105 4 (fun x => (if x<2732 then (if x<1764 then (if x<1740 then 0 else 0) else (if x<2710 then 1 else 2)) else (if x<3214 then (if x<3130 then 1 else 0) else (if x<3228 then 2 else (if x<3252 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1106 : Finset ℕ := ([132,1594,1642,1678,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3192,3214,3228,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1106 1594 4
  · have he : independentCachedBranchMembers1106.erase 1594=independentCachedBranchMembers1104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1104
  · have he : independentCachedBranchMembers1106.filter (independentCachedEdge 1594)=independentCachedBranchMembers1105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1105
def independentCachedBranchMembers1107 : Finset ℕ := ([1594,1642,1678,1702,2650,2674,2710,2758,3130,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1107 4 (fun x => (if x<2674 then (if x<1678 then (if x<1642 then 0 else 1) else (if x<1702 then 0 else (if x<2650 then 1 else 1))) else (if x<2758 then (if x<2710 then 0 else 1) else (if x<3130 then 0 else (if x<3214 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1108 : Finset ℕ := ([132,252,1594,1642,1678,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3192,3214,3228,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1108 252 4
  · have he : independentCachedBranchMembers1108.erase 252=independentCachedBranchMembers1106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1106
  · have he : independentCachedBranchMembers1108.filter (independentCachedEdge 252)=independentCachedBranchMembers1107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1107
def independentCachedBranchMembers1109 : Finset ℕ := ([1642,1692,1702,1764,2650,2710,2732,2772,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1109 4 (fun x => (if x<2710 then (if x<1702 then (if x<1692 then 0 else 1) else (if x<1764 then 0 else (if x<2650 then 1 else 0))) else (if x<2772 then (if x<2732 then 0 else 1) else (if x<3228 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1110 : Finset ℕ := ([48,132,252,1594,1642,1678,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3192,3214,3228,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1110 48 4
  · have he : independentCachedBranchMembers1110.erase 48=independentCachedBranchMembers1108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1108
  · have he : independentCachedBranchMembers1110.filter (independentCachedEdge 48)=independentCachedBranchMembers1109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1109
def independentCachedBranchMembers1111 : Finset ℕ := ([1594,1678,1692,1764,2674,2732,2758,2772,3130,3214,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1111 4 (fun x => (if x<2758 then (if x<1764 then (if x<1678 then 0 else (if x<1692 then 0 else 1)) else (if x<2674 then 1 else (if x<2732 then 0 else 1))) else (if x<3214 then (if x<2772 then 0 else (if x<3130 then 1 else 2)) else (if x<3228 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1112 : Finset ℕ := ([48,72,132,252,1594,1642,1678,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3192,3214,3228,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1112 72 4
  · have he : independentCachedBranchMembers1112.erase 72=independentCachedBranchMembers1110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1110
  · have he : independentCachedBranchMembers1112.filter (independentCachedEdge 72)=independentCachedBranchMembers1111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1111
def independentCachedBranchMembers1113 : Finset ℕ := ([252,1594,1692,1702,1740,2674,2772,3192,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1113 4 (fun x => (if x<2674 then (if x<1692 then (if x<1594 then 0 else 1) else (if x<1702 then 0 else (if x<1740 then 1 else 2))) else (if x<3214 then (if x<2772 then 2 else (if x<3192 then 0 else 1)) else (if x<3252 then 2 else (if x<3300 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1114 : Finset ℕ := ([1692,1702,2772,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1114 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1114 3 (fun x => (if x<2772 then (if x<1702 then 0 else 0) else (if x<3300 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1115 : Finset ℕ := ([48,252,1594,1692,1702,1740,2674,2772,3192,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1115 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1115 48 3
  · have he : independentCachedBranchMembers1115.erase 48=independentCachedBranchMembers1113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1113
  · have he : independentCachedBranchMembers1115.filter (independentCachedEdge 48)=independentCachedBranchMembers1114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1114
def independentCachedBranchMembers1116 : Finset ℕ := ([48,252,1594,1692,3214,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1116 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1116 3 (fun x => (if x<1692 then (if x<252 then 0 else (if x<1594 then 0 else 1)) else (if x<3214 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1117 : Finset ℕ := ([48,252,1594,1642,1692,1702,1740,2674,2772,3192,3214,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1117 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1117 1642 3
  · have he : independentCachedBranchMembers1117.erase 1642=independentCachedBranchMembers1115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1115
  · have he : independentCachedBranchMembers1117.filter (independentCachedEdge 1642)=independentCachedBranchMembers1116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1116
def independentCachedBranchMembers1118 : Finset ℕ := ([48,72,132,252,1594,1642,1678,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1118 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1118 3238 4
  · have he : independentCachedBranchMembers1118.erase 3238=independentCachedBranchMembers1112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1112
  · have he : independentCachedBranchMembers1118.filter (independentCachedEdge 3238)=independentCachedBranchMembers1117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1117
def independentCachedBranchMembers1119 : Finset ℕ := ([252,1642,1678,1740,1764,2732,2758,3130,3192,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1119 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1119 4 (fun x => (if x<2732 then (if x<1678 then (if x<1642 then 0 else 1) else (if x<1740 then 1 else (if x<1764 then 0 else 1))) else (if x<3192 then (if x<2758 then 0 else (if x<3130 then 2 else 2)) else (if x<3228 then 3 else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1120 : Finset ℕ := ([1642,1764,2732,3228] : List ℕ).toFinset
theorem independentCachedBranchBound1120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1120 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1120 3 (fun x => (if x<2732 then (if x<1764 then 0 else 0) else (if x<3228 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1121 : Finset ℕ := ([48,252,1642,1678,1740,1764,2732,2758,3130,3192,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1121 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1121 48 3
  · have he : independentCachedBranchMembers1121.erase 48=independentCachedBranchMembers1119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1119
  · have he : independentCachedBranchMembers1121.filter (independentCachedEdge 48)=independentCachedBranchMembers1120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1120
def independentCachedBranchMembers1122 : Finset ℕ := ([48,252,1678,1764,3130,3228] : List ℕ).toFinset
theorem independentCachedBranchBound1122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1122 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1122 3 (fun x => (if x<1764 then (if x<252 then 0 else (if x<1678 then 0 else 1)) else (if x<3130 then 1 else (if x<3228 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1123 : Finset ℕ := ([48,252,1642,1678,1702,1740,1764,2732,2758,3130,3192,3228,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1123 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1123 1702 3
  · have he : independentCachedBranchMembers1123.erase 1702=independentCachedBranchMembers1121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1121
  · have he : independentCachedBranchMembers1123.filter (independentCachedEdge 1702)=independentCachedBranchMembers1122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1122
def independentCachedBranchMembers1124 : Finset ℕ := ([48,72,132,252,1594,1642,1678,1692,1702,1740,1764,2650,2674,2710,2732,2758,2772,3130,3178,3192,3214,3228,3238,3252,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1124 3178 4
  · have he : independentCachedBranchMembers1124.erase 3178=independentCachedBranchMembers1118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1118
  · have he : independentCachedBranchMembers1124.filter (independentCachedEdge 3178)=independentCachedBranchMembers1123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1123
def independentCachedBranchMembers1125 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800,3102,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1125 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1125 2646 5
  · have he : independentCachedBranchMembers1125.erase 2646=independentCachedBranchMembers1101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1101
  · have he : independentCachedBranchMembers1125.filter (independentCachedEdge 2646)=independentCachedBranchMembers1124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1124
def independentCachedBranchMembers1126 : Finset ℕ := ([132,252,1628,1652,1692,1720,1740,1764,1768,2620,2668,2732,2772,2776,2800,3164,3192,3228,3252,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1126 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1126 5 (fun x => (if x<2732 then (if x<1720 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1652 then 1 else (if x<1692 then 2 else 0))) else (if x<1768 then (if x<1740 then 1 else (if x<1764 then 2 else 0)) else (if x<2620 then 3 else (if x<2668 then 1 else 2)))) else (if x<3192 then (if x<2776 then (if x<2772 then 0 else 0) else (if x<2800 then 1 else (if x<3164 then 3 else 2))) else (if x<3276 then (if x<3228 then 1 else (if x<3252 then 1 else 0)) else (if x<3300 then 0 else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1127 : Finset ℕ := ([1652,1692,1720,1764,2620,2732,2772,2800,3228,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1127 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1127 4 (fun x => (if x<2732 then (if x<1720 then (if x<1692 then 0 else 0) else (if x<1764 then 1 else (if x<2620 then 1 else 0))) else (if x<2800 then (if x<2772 then 1 else 0) else (if x<3228 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1128 : Finset ℕ := ([72,132,252,1628,1652,1692,1720,1740,1764,1768,2620,2668,2732,2772,2776,2800,3164,3192,3228,3252,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1128 72 4
  · have he : independentCachedBranchMembers1128.erase 72=independentCachedBranchMembers1126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1126
  · have he : independentCachedBranchMembers1128.filter (independentCachedEdge 72)=independentCachedBranchMembers1127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1127
def independentCachedBranchMembers1129 : Finset ℕ := ([1628,1692,1764,1768,2668,2732,2772,2776,3164,3228,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1129 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1129 4 (fun x => (if x<2772 then (if x<1768 then (if x<1692 then 0 else (if x<1764 then 1 else 0)) else (if x<2668 then 1 else (if x<2732 then 0 else 1))) else (if x<3228 then (if x<2776 then 0 else (if x<3164 then 1 else 2)) else (if x<3300 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1130 : Finset ℕ := ([48,72,132,252,1628,1652,1692,1720,1740,1764,1768,2620,2668,2732,2772,2776,2800,3164,3192,3228,3252,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1130 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1130 48 4
  · have he : independentCachedBranchMembers1130.erase 48=independentCachedBranchMembers1128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1128
  · have he : independentCachedBranchMembers1130.filter (independentCachedEdge 48)=independentCachedBranchMembers1129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1129
def independentCachedBranchMembers1131 : Finset ℕ := ([132,1628,1720,1740,1764,2668,2772,3192,3228,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1131 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1131 4 (fun x => (if x<2668 then (if x<1720 then (if x<1628 then 0 else 1) else (if x<1740 then 1 else (if x<1764 then 0 else 1))) else (if x<3228 then (if x<2772 then 2 else (if x<3192 then 0 else 2)) else (if x<3252 then 0 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1132 : Finset ℕ := ([1720,1764,2772,3228] : List ℕ).toFinset
theorem independentCachedBranchBound1132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1132 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1132 3 (fun x => (if x<2772 then (if x<1764 then 0 else 0) else (if x<3228 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1133 : Finset ℕ := ([72,132,1628,1720,1740,1764,2668,2772,3192,3228,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1133 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1133 72 3
  · have he : independentCachedBranchMembers1133.erase 72=independentCachedBranchMembers1131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1131
  · have he : independentCachedBranchMembers1133.filter (independentCachedEdge 72)=independentCachedBranchMembers1132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1132
def independentCachedBranchMembers1134 : Finset ℕ := ([72,132,1628,1764,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1134 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1134 3 (fun x => (if x<1764 then (if x<132 then 0 else (if x<1628 then 0 else 1)) else (if x<3228 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1135 : Finset ℕ := ([72,132,1628,1652,1720,1740,1764,2668,2772,3192,3228,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1135 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1135 1652 3
  · have he : independentCachedBranchMembers1135.erase 1652=independentCachedBranchMembers1133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1133
  · have he : independentCachedBranchMembers1135.filter (independentCachedEdge 1652)=independentCachedBranchMembers1134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1134
def independentCachedBranchMembers1136 : Finset ℕ := ([48,72,132,252,1628,1652,1692,1720,1740,1764,1768,2620,2668,2732,2772,2776,2800,3164,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1136 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1136 3256 4
  · have he : independentCachedBranchMembers1136.erase 3256=independentCachedBranchMembers1130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1130
  · have he : independentCachedBranchMembers1136.filter (independentCachedEdge 3256)=independentCachedBranchMembers1135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1135
def independentCachedBranchMembers1137 : Finset ℕ := ([132,1652,1692,1740,1768,2732,2776,3164,3192,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1137 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1137 4 (fun x => (if x<2732 then (if x<1692 then (if x<1652 then 0 else 1) else (if x<1740 then 0 else (if x<1768 then 1 else 2))) else (if x<3192 then (if x<2776 then 0 else (if x<3164 then 2 else 1)) else (if x<3252 then 2 else (if x<3300 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1138 : Finset ℕ := ([1652,1692,2732,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1138 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1138 3 (fun x => (if x<2732 then (if x<1692 then 0 else 0) else (if x<3300 then 1 else 1)))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1139 : Finset ℕ := ([72,132,1652,1692,1740,1768,2732,2776,3164,3192,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1139 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1139 72 3
  · have he : independentCachedBranchMembers1139.erase 72=independentCachedBranchMembers1137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1137
  · have he : independentCachedBranchMembers1139.filter (independentCachedEdge 72)=independentCachedBranchMembers1138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1138
def independentCachedBranchMembers1140 : Finset ℕ := ([72,132,1692,1768,3164,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1140 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1140 3 (fun x => (if x<1768 then (if x<132 then 0 else (if x<1692 then 0 else 1)) else (if x<3164 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1141 : Finset ℕ := ([72,132,1652,1692,1720,1740,1768,2732,2776,3164,3192,3252,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1141 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1141 1720 3
  · have he : independentCachedBranchMembers1141.erase 1720=independentCachedBranchMembers1139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1139
  · have he : independentCachedBranchMembers1141.filter (independentCachedEdge 1720)=independentCachedBranchMembers1140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1140
def independentCachedBranchMembers1142 : Finset ℕ := ([48,72,132,252,1628,1652,1692,1720,1740,1764,1768,2620,2668,2732,2772,2776,2800,3164,3188,3192,3228,3252,3256,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1142 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1142 3188 4
  · have he : independentCachedBranchMembers1142.erase 3188=independentCachedBranchMembers1136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1136
  · have he : independentCachedBranchMembers1142.filter (independentCachedEdge 3188)=independentCachedBranchMembers1141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1141
def independentCachedBranchMembers1143 : Finset ℕ := ([48,72,132,252,1590,1594,1614,1628,1642,1652,1678,1692,1702,1720,1740,1746,1764,1768,2606,2620,2646,2650,2668,2674,2710,2714,2732,2738,2758,2762,2772,2776,2786,2800,3102,3126,3130,3150,3164,3178,3188,3192,3214,3228,3238,3252,3256,3276,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1143 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1143 2606 5
  · have he : independentCachedBranchMembers1143.erase 2606=independentCachedBranchMembers1125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1125
  · have he : independentCachedBranchMembers1143.filter (independentCachedEdge 2606)=independentCachedBranchMembers1142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1142
def independentCachedBranchMembers1144 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1144 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1144 2770 6
  · have he : independentCachedBranchMembers1144.erase 2770=independentCachedBranchMembers1032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1032
  · have he : independentCachedBranchMembers1144.filter (independentCachedEdge 2770)=independentCachedBranchMembers1143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1143
def independentCachedBranchMembers1145 : Finset ℕ := ([1590,1628,1642,1708,1734,1776,2620,2650,2662,2710,2730,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1145 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1145 6 (fun x => (if x<3118 then (if x<2650 then (if x<1708 then (if x<1628 then 0 else (if x<1642 then 0 else 0)) else (if x<1776 then (if x<1734 then 0 else 0) else (if x<2620 then 0 else 1))) else (if x<2730 then (if x<2662 then 1 else (if x<2710 then 1 else 1)) else (if x<2800 then (if x<2764 then 1 else 1) else (if x<3102 then 1 else 2)))) else (if x<3252 then (if x<3188 then (if x<3150 then 3 else (if x<3186 then 4 else 2)) else (if x<3214 then (if x<3192 then 3 else 4) else (if x<3250 then 5 else 3))) else (if x<3288 then (if x<3282 then (if x<3256 then 2 else 5) else (if x<3284 then 4 else 5)) else (if x<3300 then (if x<3298 then 2 else 5) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1146 : Finset ℕ := ([1642,1776,2650,2662,2710,2730,3118,3192,3214,3250,3252,3288,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1146 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1146 5 (fun x => (if x<3192 then (if x<2662 then (if x<1776 then 0 else (if x<2650 then 0 else 1)) else (if x<2730 then (if x<2710 then 1 else 1) else (if x<3118 then 1 else 0))) else (if x<3252 then (if x<3214 then 0 else (if x<3250 then 2 else 2)) else (if x<3298 then (if x<3288 then 0 else 2) else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1147 : Finset ℕ := ([1590,1628,1642,1708,1734,1776,2620,2646,2650,2662,2710,2730,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1147 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1147 2646 5
  · have he : independentCachedBranchMembers1147.erase 2646=independentCachedBranchMembers1145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1145
  · have he : independentCachedBranchMembers1147.filter (independentCachedEdge 2646)=independentCachedBranchMembers1146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1146
def independentCachedBranchMembers1148 : Finset ℕ := ([1628,1708,1776,2620,2650,2730,2764,3102,3118,3186,3192,3250,3256,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1148 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1148 5 (fun x => (if x<3102 then (if x<2620 then (if x<1708 then 0 else (if x<1776 then 0 else 0)) else (if x<2730 then (if x<2650 then 1 else 1) else (if x<2764 then 1 else 1))) else (if x<3250 then (if x<3186 then (if x<3118 then 2 else 3) else (if x<3192 then 2 else 3)) else (if x<3284 then (if x<3256 then 3 else 2) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1149 : Finset ℕ := ([1590,1628,1642,1708,1734,1776,2620,2646,2650,2662,2710,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1149 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1149 2762 5
  · have he : independentCachedBranchMembers1149.erase 2762=independentCachedBranchMembers1147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1147
  · have he : independentCachedBranchMembers1149.filter (independentCachedEdge 2762)=independentCachedBranchMembers1148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1148
def independentCachedBranchMembers1150 : Finset ℕ := ([1590,1734,1776,2620,2662,2710,2764,3118,3150,3188,3192,3250,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1150 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1150 5 (fun x => (if x<3118 then (if x<2620 then (if x<1734 then 0 else (if x<1776 then 0 else 0)) else (if x<2710 then (if x<2662 then 1 else 1) else (if x<2764 then 1 else 1))) else (if x<3250 then (if x<3188 then (if x<3150 then 2 else 3) else (if x<3192 then 2 else 3)) else (if x<3300 then (if x<3282 then 2 else 3) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1151 : Finset ℕ := ([1590,1628,1642,1708,1734,1776,2620,2646,2650,2662,2710,2716,2730,2762,2764,2800,3102,3118,3150,3186,3188,3192,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1151 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1151 2716 5
  · have he : independentCachedBranchMembers1151.erase 2716=independentCachedBranchMembers1149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1149
  · have he : independentCachedBranchMembers1151.filter (independentCachedEdge 2716)=independentCachedBranchMembers1150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1150
end EntropyDesigns.QuadraticRefinement
