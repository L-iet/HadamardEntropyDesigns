/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch67
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4960 : Finset ℕ := ([48,68,136,222,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4960 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4960 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4960 222 4
  · have he : independentCachedBranchMembers4960.erase 222=independentCachedBranchMembers4958 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4958
  · have he : independentCachedBranchMembers4960.filter (independentCachedEdge 222)=independentCachedBranchMembers4959 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4959
def independentCachedBranchMembers4961 : Finset ℕ := ([68,136,1614,1644,1650,1692,2652,2702,2732,2738,3158,3178,3188,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4961 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4961 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4961 4 (fun x => (if x<2732 then (if x<1650 then (if x<1614 then (if x<136 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<2652 then (if x<1692 then 1 else 2) else (if x<2702 then 2 else 1))) else (if x<3188 then (if x<3158 then (if x<2738 then 2 else 1) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3226 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4962 : Finset ℕ := ([48,68,136,192,222,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4962 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4962 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4962 192 4
  · have he : independentCachedBranchMembers4962.erase 192=independentCachedBranchMembers4960 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4960
  · have he : independentCachedBranchMembers4962.filter (independentCachedEdge 192)=independentCachedBranchMembers4961 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4961
def independentCachedBranchMembers4963 : Finset ℕ := ([48,252,1614,1692,1738,1748,2652,2702,2758,2776,3132,3178,3188,3238,3256,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4963 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4963 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4963 4 (fun x => (if x<2758 then (if x<1738 then (if x<1614 then (if x<252 then 0 else 0) else (if x<1692 then 1 else 1)) else (if x<2652 then (if x<1748 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3188 then (if x<3132 then (if x<2776 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3256 then (if x<3238 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4964 : Finset ℕ := ([18,48,68,136,192,222,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4964 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4964 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4964 18 4
  · have he : independentCachedBranchMembers4964.erase 18=independentCachedBranchMembers4962 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4962
  · have he : independentCachedBranchMembers4964.filter (independentCachedEdge 18)=independentCachedBranchMembers4963 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4963
def independentCachedBranchMembers4965 : Finset ℕ := ([68,136,1594,1738,1748,1768,2614,2758,2776,2788,3158,3178,3188,3226,3238,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4965 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4965 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4965 4 (fun x => (if x<2776 then (if x<1748 then (if x<1594 then (if x<136 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2758 then 1 else 1))) else (if x<3188 then (if x<3158 then (if x<2788 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3238 then (if x<3226 then 3 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4966 : Finset ℕ := ([12,18,48,68,136,192,222,252,1594,1614,1644,1650,1692,1738,1748,1768,2614,2652,2702,2732,2738,2758,2776,2788,3072,3102,3132,3158,3178,3188,3226,3238,3256,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4966 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4966 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4966 12 4
  · have he : independentCachedBranchMembers4966.erase 12=independentCachedBranchMembers4964 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4964
  · have he : independentCachedBranchMembers4966.filter (independentCachedEdge 12)=independentCachedBranchMembers4965 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4965
def independentCachedBranchMembers4967 : Finset ℕ := ([12,18,40,48,66,68,136,144,192,222,250,252,1594,1596,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1738,1740,1746,1748,1768,1776,2606,2614,2650,2652,2662,2680,2702,2710,2730,2732,2738,2740,2758,2776,2786,2788,3072,3102,3130,3132,3150,3158,3178,3180,3186,3188,3226,3228,3238,3256,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4967 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4967 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4967 1642 5
  · have he : independentCachedBranchMembers4967.erase 1642=independentCachedBranchMembers4947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4947
  · have he : independentCachedBranchMembers4967.filter (independentCachedEdge 1642)=independentCachedBranchMembers4966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4966
def independentCachedBranchMembers4968 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound4968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4968 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4968 2726 6
  · have he : independentCachedBranchMembers4968.erase 2726=independentCachedBranchMembers4708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4708
  · have he : independentCachedBranchMembers4968.filter (independentCachedEdge 2726)=independentCachedBranchMembers4967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4967
def independentCachedBranchMembers4969 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2620,2646,2662,2668,2674,2680,2714,2730,2740,2762,2772,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4969 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4969 6 (fun x => (if x<2762 then (if x<2646 then (if x<1714 then (if x<1652 then 0 else (if x<1708 then 0 else 0)) else (if x<1752 then (if x<1734 then 0 else 0) else (if x<2620 then 0 else 1))) else (if x<2680 then (if x<2668 then (if x<2662 then 1 else 2) else (if x<2674 then 3 else 3)) else (if x<2730 then (if x<2714 then 2 else 1) else (if x<2740 then 2 else 2)))) else (if x<3222 then (if x<3130 then (if x<2800 then (if x<2772 then 3 else 3) else (if x<3118 then 1 else 4)) else (if x<3162 then (if x<3150 then 5 else 5) else (if x<3188 then 4 else 1))) else (if x<3276 then (if x<3238 then (if x<3228 then 4 else 5) else (if x<3256 then 2 else 1)) else (if x<3298 then (if x<3282 then 3 else 1) else (if x<3304 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4970 : Finset ℕ := ([1642,1714,1752,2662,2668,2714,2740,2772,2800,3118,3150,3222,3228,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4970 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4970 5 (fun x => (if x<2772 then (if x<2662 then (if x<1714 then 0 else (if x<1752 then 0 else 0)) else (if x<2714 then (if x<2668 then 1 else 2) else (if x<2740 then 3 else 1))) else (if x<3222 then (if x<3118 then (if x<2800 then 2 else 3) else (if x<3150 then 2 else 1)) else (if x<3256 then (if x<3228 then 2 else 1) else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4971 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2620,2646,2662,2668,2674,2680,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4971 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4971 2788 5
  · have he : independentCachedBranchMembers4971.erase 2788=independentCachedBranchMembers4969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4969
  · have he : independentCachedBranchMembers4971.filter (independentCachedEdge 2788)=independentCachedBranchMembers4970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4970
def independentCachedBranchMembers4972 : Finset ℕ := ([1642,1714,1752,2674,2680,2714,2730,2762,2800,3130,3162,3256,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4972 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4972 5 (fun x => (if x<2762 then (if x<2674 then (if x<1714 then 0 else (if x<1752 then 0 else 0)) else (if x<2714 then (if x<2680 then 1 else 2) else (if x<2730 then 1 else 2))) else (if x<3256 then (if x<3130 then (if x<2800 then 3 else 3) else (if x<3162 then 1 else 4)) else (if x<3298 then (if x<3282 then 2 else 1) else (if x<3304 then 3 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4973 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2620,2646,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4973 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4973 2702 5
  · have he : independentCachedBranchMembers4973.erase 2702=independentCachedBranchMembers4971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4971
  · have he : independentCachedBranchMembers4973.filter (independentCachedEdge 2702)=independentCachedBranchMembers4972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4972
def independentCachedBranchMembers4974 : Finset ℕ := ([1642,1708,1734,2620,2646,2668,2680,2730,2772,3118,3130,3222,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4974 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4974 5 (fun x => (if x<2730 then (if x<2620 then (if x<1708 then 0 else (if x<1734 then 0 else 0)) else (if x<2668 then (if x<2646 then 1 else 1) else (if x<2680 then 2 else 3))) else (if x<3222 then (if x<3118 then (if x<2772 then 2 else 3) else (if x<3130 then 2 else 3)) else (if x<3282 then (if x<3256 then 3 else 1) else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4975 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4975 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4975 2652 5
  · have he : independentCachedBranchMembers4975.erase 2652=independentCachedBranchMembers4973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4973
  · have he : independentCachedBranchMembers4975.filter (independentCachedEdge 2652)=independentCachedBranchMembers4974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4974
def independentCachedBranchMembers4976 : Finset ℕ := ([1642,1708,1734,2620,2646,2662,2674,2740,2762,3150,3162,3228,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4976 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4976 5 (fun x => (if x<2740 then (if x<2620 then (if x<1708 then 0 else (if x<1734 then 0 else 0)) else (if x<2662 then (if x<2646 then 1 else 1) else (if x<2674 then 2 else 3))) else (if x<3228 then (if x<3150 then (if x<2762 then 2 else 3) else (if x<3162 then 2 else 3)) else (if x<3282 then (if x<3256 then 2 else 1) else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4977 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4977 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4977 2614 5
  · have he : independentCachedBranchMembers4977.erase 2614=independentCachedBranchMembers4975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4975
  · have he : independentCachedBranchMembers4977.filter (independentCachedEdge 2614)=independentCachedBranchMembers4976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4976
def independentCachedBranchMembers4978 : Finset ℕ := ([1642,1708,1752,2620,2652,2662,2674,2702,2714,2740,2772,3118,3130,3150,3162,3188,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4978 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4978 5 (fun x => (if x<2772 then (if x<2662 then (if x<1752 then (if x<1708 then 0 else 0) else (if x<2620 then 0 else (if x<2652 then 1 else 2))) else (if x<2702 then (if x<2674 then 1 else 2) else (if x<2714 then 1 else (if x<2740 then 2 else 2)))) else (if x<3188 then (if x<3130 then (if x<3118 then 1 else 0) else (if x<3150 then 3 else (if x<3162 then 3 else 0))) else (if x<3238 then (if x<3228 then 1 else 0) else (if x<3282 then 3 else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4979 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4979 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4979 1768 5
  · have he : independentCachedBranchMembers4979.erase 1768=independentCachedBranchMembers4977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4977
  · have he : independentCachedBranchMembers4979.filter (independentCachedEdge 1768)=independentCachedBranchMembers4978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4978
def independentCachedBranchMembers4980 : Finset ℕ := ([1642,1708,1752,2614,2646,2668,2680,2730,2762,2788,2800,3118,3130,3150,3162,3188,3228,3238,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4980 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4980 5 (fun x => (if x<2800 then (if x<2668 then (if x<1752 then (if x<1708 then 0 else 0) else (if x<2614 then 0 else (if x<2646 then 1 else 2))) else (if x<2730 then (if x<2680 then 1 else 2) else (if x<2762 then 1 else (if x<2788 then 2 else 2)))) else (if x<3188 then (if x<3130 then (if x<3118 then 1 else 0) else (if x<3150 then 3 else (if x<3162 then 3 else 0))) else (if x<3238 then (if x<3228 then 1 else 0) else (if x<3282 then 3 else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4981 : Finset ℕ := ([1642,1652,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4981 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4981 1692 5
  · have he : independentCachedBranchMembers4981.erase 1692=independentCachedBranchMembers4979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4979
  · have he : independentCachedBranchMembers4981.filter (independentCachedEdge 1692)=independentCachedBranchMembers4980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4980
def independentCachedBranchMembers4982 : Finset ℕ := ([1642,1714,1734,2614,2620,2674,2680,2714,2730,2772,2788,3130,3150,3188,3222,3228,3238,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4982 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4982 5 (fun x => (if x<2788 then (if x<2674 then (if x<1734 then (if x<1714 then 0 else 0) else (if x<2614 then 0 else (if x<2620 then 1 else 2))) else (if x<2714 then (if x<2680 then 2 else 1) else (if x<2730 then 1 else (if x<2772 then 2 else 1)))) else (if x<3228 then (if x<3150 then (if x<3130 then 2 else 0) else (if x<3188 then 0 else (if x<3222 then 1 else 0))) else (if x<3282 then (if x<3238 then 3 else 3) else (if x<3298 then 3 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4983 : Finset ℕ := ([1614,1642,1652,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4983 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4983 1614 5
  · have he : independentCachedBranchMembers4983.erase 1614=independentCachedBranchMembers4981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4981
  · have he : independentCachedBranchMembers4983.filter (independentCachedEdge 1614)=independentCachedBranchMembers4982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4982
def independentCachedBranchMembers4984 : Finset ℕ := ([1642,1714,1734,2646,2652,2662,2668,2702,2740,2762,2800,3130,3150,3188,3222,3228,3238,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4984 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4984 5 (fun x => (if x<2800 then (if x<2662 then (if x<1734 then (if x<1714 then 0 else 0) else (if x<2646 then 0 else (if x<2652 then 1 else 2))) else (if x<2702 then (if x<2668 then 2 else 1) else (if x<2740 then 1 else (if x<2762 then 1 else 2)))) else (if x<3228 then (if x<3150 then (if x<3130 then 2 else 0) else (if x<3188 then 0 else (if x<3222 then 1 else 0))) else (if x<3282 then (if x<3238 then 3 else 3) else (if x<3298 then 3 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4985 : Finset ℕ := ([1594,1614,1642,1652,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4985 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4985 1594 5
  · have he : independentCachedBranchMembers4985.erase 1594=independentCachedBranchMembers4983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4983
  · have he : independentCachedBranchMembers4985.filter (independentCachedEdge 1594)=independentCachedBranchMembers4984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4984
def independentCachedBranchMembers4986 : Finset ℕ := ([1642,1652,1708,1714,1734,1752,2614,2620,2646,2652,2702,2714,2788,2800,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4986 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4986 5 (fun x => (if x<2714 then (if x<1752 then (if x<1708 then (if x<1652 then 0 else 0) else (if x<1714 then 0 else (if x<1734 then 0 else 0))) else (if x<2646 then (if x<2614 then 0 else (if x<2620 then 1 else 2)) else (if x<2652 then 2 else (if x<2702 then 1 else 1)))) else (if x<3150 then (if x<2800 then (if x<2788 then 2 else 1) else (if x<3118 then 2 else (if x<3130 then 3 else 4))) else (if x<3228 then (if x<3162 then 4 else (if x<3222 then 3 else 3)) else (if x<3298 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4987 : Finset ℕ := ([1594,1614,1642,1652,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4987 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4987 3178 5
  · have he : independentCachedBranchMembers4987.erase 3178=independentCachedBranchMembers4985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4985
  · have he : independentCachedBranchMembers4987.filter (independentCachedEdge 3178)=independentCachedBranchMembers4986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4986
def independentCachedBranchMembers4988 : Finset ℕ := ([1642,1692,1714,1734,1768,2614,2646,2668,2680,2702,2714,2740,2772,3118,3130,3150,3162,3188,3222,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4988 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4988 5 (fun x => (if x<2740 then (if x<2614 then (if x<1714 then (if x<1692 then 0 else 1) else (if x<1734 then 0 else (if x<1768 then 0 else 1))) else (if x<2680 then (if x<2646 then 2 else (if x<2668 then 3 else 2)) else (if x<2702 then 3 else (if x<2714 then 2 else 3)))) else (if x<3162 then (if x<3118 then (if x<2772 then 3 else 2) else (if x<3130 then 2 else (if x<3150 then 0 else 0))) else (if x<3256 then (if x<3188 then 3 else (if x<3222 then 2 else 0)) else (if x<3276 then 1 else (if x<3298 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4989 : Finset ℕ := ([1594,1614,1642,1652,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4989 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4989 1762 5
  · have he : independentCachedBranchMembers4989.erase 1762=independentCachedBranchMembers4987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4987
  · have he : independentCachedBranchMembers4989.filter (independentCachedEdge 1762)=independentCachedBranchMembers4988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4988
def independentCachedBranchMembers4990 : Finset ℕ := ([1642,1692,1714,1734,1768,2620,2652,2662,2674,2730,2762,2788,2800,3118,3130,3150,3162,3188,3222,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4990 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4990 5 (fun x => (if x<2788 then (if x<2620 then (if x<1714 then (if x<1692 then 0 else 1) else (if x<1734 then 0 else (if x<1768 then 0 else 1))) else (if x<2674 then (if x<2652 then 2 else (if x<2662 then 3 else 2)) else (if x<2730 then 3 else (if x<2762 then 2 else 3)))) else (if x<3162 then (if x<3118 then (if x<2800 then 3 else 2) else (if x<3130 then 2 else (if x<3150 then 0 else 0))) else (if x<3256 then (if x<3188 then 3 else (if x<3222 then 2 else 0)) else (if x<3276 then 1 else (if x<3298 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4991 : Finset ℕ := ([1594,1614,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4991 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4991 1686 5
  · have he : independentCachedBranchMembers4991.erase 1686=independentCachedBranchMembers4989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4989
  · have he : independentCachedBranchMembers4991.filter (independentCachedEdge 1686)=independentCachedBranchMembers4990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4990
end EntropyDesigns.QuadraticRefinement
