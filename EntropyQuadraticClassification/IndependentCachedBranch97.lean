/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch96
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5888 : Finset ℕ := ([1594,1614,1628,1644,1650,1678,1692,1708,1714,1734,1738,1748,1752,1764,1768,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5888 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5888 1614 4
  · have he : independentCachedBranchMembers5888.erase 1614=independentCachedBranchMembers5886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5886
  · have he : independentCachedBranchMembers5888.filter (independentCachedEdge 1614)=independentCachedBranchMembers5887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5887
def independentCachedBranchMembers5889 : Finset ℕ := ([1594,1650,1714,1738,1752,1768,3072,3162,3178,3192,3226,3242,3256,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5889 4 (fun x => (if x<3178 then (if x<1752 then (if x<1714 then (if x<1650 then 0 else 1) else (if x<1738 then 2 else 0)) else (if x<3072 then (if x<1768 then 1 else 2) else (if x<3162 then 3 else 0))) else (if x<3256 then (if x<3226 then (if x<3192 then 3 else 1) else (if x<3242 then 3 else 0)) else (if x<3298 then (if x<3282 then 2 else 1) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5890 : Finset ℕ := ([1590,1594,1614,1628,1644,1650,1678,1692,1708,1714,1734,1738,1748,1752,1764,1768,3072,3102,3118,3132,3158,3162,3174,3178,3188,3192,3222,3226,3238,3242,3252,3256,3276,3282,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5890 1590 4
  · have he : independentCachedBranchMembers5890.erase 1590=independentCachedBranchMembers5888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5888
  · have he : independentCachedBranchMembers5890.filter (independentCachedEdge 1590)=independentCachedBranchMembers5889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5889
def independentCachedBranchMembers5891 : Finset ℕ := ([1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5891 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5891 1740 5
  · have he : independentCachedBranchMembers5891.erase 1740=independentCachedBranchMembers5869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5869
  · have he : independentCachedBranchMembers5891.filter (independentCachedEdge 1740)=independentCachedBranchMembers5890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5890
def independentCachedBranchMembers5892 : Finset ℕ := ([12,18,34,36,40,48,66,68,72,80,130,132,136,144,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5892 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5892 2560 6
  · have he : independentCachedBranchMembers5892.erase 2560=independentCachedBranchMembers5670 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5670
  · have he : independentCachedBranchMembers5892.filter (independentCachedEdge 2560)=independentCachedBranchMembers5891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5891
def independentCachedBranchMembers5893 : Finset ℕ := ([1596,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2668,2674,2730,2740,2758,2776,3118,3130,3158,3164,3174,3192,3214,3226,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5893 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5893 6 (fun x => (if x<2730 then (if x<1714 then (if x<1686 then (if x<1642 then (if x<1626 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1702 then (if x<1692 then 0 else 2) else (if x<1708 then 1 else 3))) else (if x<1764 then (if x<1738 then (if x<1720 then 2 else 1) else (if x<1748 then 2 else 3)) else (if x<2668 then (if x<1776 then 2 else 0) else (if x<2674 then 4 else 4)))) else (if x<3174 then (if x<3118 then (if x<2758 then (if x<2740 then 1 else 0) else (if x<2776 then 4 else 4)) else (if x<3158 then (if x<3130 then 3 else 5) else (if x<3164 then 3 else 5))) else (if x<3252 then (if x<3214 then (if x<3192 then 4 else 4) else (if x<3226 then 5 else 2)) else (if x<3282 then (if x<3276 then 2 else 2) else (if x<3298 then 4 else (if x<3304 then 2 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5894 : Finset ℕ := ([1626,1642,1714,1720,1738,1776,2674,2730,2776,3130,3192,3226,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5894 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5894 5 (fun x => (if x<2730 then (if x<1720 then (if x<1642 then 0 else (if x<1714 then 1 else 0)) else (if x<1776 then (if x<1738 then 1 else 2) else (if x<2674 then 2 else 0))) else (if x<3226 then (if x<3130 then (if x<2776 then 1 else 2) else (if x<3192 then 0 else 3)) else (if x<3298 then (if x<3282 then 3 else 0) else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5895 : Finset ℕ := ([1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2668,2674,2730,2740,2758,2776,3118,3130,3158,3164,3174,3192,3214,3226,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5895 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5895 1614 5
  · have he : independentCachedBranchMembers5895.erase 1614=independentCachedBranchMembers5893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5893
  · have he : independentCachedBranchMembers5895.filter (independentCachedEdge 1614)=independentCachedBranchMembers5894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5894
def independentCachedBranchMembers5896 : Finset ℕ := ([1596,1652,1686,1702,1714,1738,2668,2730,2758,3164,3192,3214,3226,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5896 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5896 5 (fun x => (if x<2730 then (if x<1702 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<1738 then (if x<1714 then 1 else 2) else (if x<2668 then 2 else 0))) else (if x<3214 then (if x<3164 then (if x<2758 then 1 else 0) else (if x<3192 then 1 else 0)) else (if x<3282 then (if x<3226 then 1 else 2) else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5897 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2668,2674,2730,2740,2758,2776,3118,3130,3158,3164,3174,3192,3214,3226,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5897 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5897 1590 5
  · have he : independentCachedBranchMembers5897.erase 1590=independentCachedBranchMembers5895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5895
  · have he : independentCachedBranchMembers5897.filter (independentCachedEdge 1590)=independentCachedBranchMembers5896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5896
def independentCachedBranchMembers5898 : Finset ℕ := ([1596,1614,1626,1652,1692,1702,1714,1748,2668,2730,2776,3118,3130,3164,3174,3214,3226,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5898 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5898 5 (fun x => (if x<2776 then (if x<1702 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else (if x<1692 then 1 else 1))) else (if x<1748 then (if x<1714 then 0 else 1) else (if x<2668 then 0 else (if x<2730 then 2 else 2)))) else (if x<3214 then (if x<3130 then (if x<3118 then 2 else 0) else (if x<3164 then 3 else (if x<3174 then 0 else 3))) else (if x<3252 then (if x<3226 then 3 else 1) else (if x<3282 then 0 else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5899 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2668,2674,2730,2740,2758,2776,2792,3118,3130,3158,3164,3174,3192,3214,3226,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5899 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5899 2792 5
  · have he : independentCachedBranchMembers5899.erase 2792=independentCachedBranchMembers5897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5897
  · have he : independentCachedBranchMembers5899.filter (independentCachedEdge 2792)=independentCachedBranchMembers5898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5898
def independentCachedBranchMembers5900 : Finset ℕ := ([1590,1596,1626,1642,1714,1720,1748,1764,2674,2730,2758,3130,3158,3164,3174,3214,3252,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5900 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5900 5 (fun x => (if x<2758 then (if x<1720 then (if x<1626 then (if x<1596 then 0 else 1) else (if x<1642 then 0 else (if x<1714 then 1 else 1))) else (if x<1764 then (if x<1748 then 0 else 0) else (if x<2674 then 1 else (if x<2730 then 2 else 2)))) else (if x<3214 then (if x<3158 then (if x<3130 then 2 else 0) else (if x<3164 then 0 else (if x<3174 then 3 else 3))) else (if x<3282 then (if x<3252 then 2 else 0) else (if x<3298 then 3 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5901 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2668,2674,2702,2730,2740,2758,2776,2792,3118,3130,3158,3164,3174,3192,3214,3226,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5901 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5901 2702 5
  · have he : independentCachedBranchMembers5901.erase 2702=independentCachedBranchMembers5899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5899
  · have he : independentCachedBranchMembers5901.filter (independentCachedEdge 2702)=independentCachedBranchMembers5900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5900
def independentCachedBranchMembers5902 : Finset ℕ := ([1590,1642,1686,1708,1720,1738,1764,1776,2668,2730,2776,3118,3130,3164,3174,3214,3226,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5902 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5902 5 (fun x => (if x<2776 then (if x<1738 then (if x<1686 then (if x<1642 then 0 else 0) else (if x<1708 then 1 else (if x<1720 then 0 else 1))) else (if x<1776 then (if x<1764 then 1 else 1) else (if x<2668 then 0 else (if x<2730 then 2 else 2)))) else (if x<3214 then (if x<3130 then (if x<3118 then 2 else 0) else (if x<3164 then 3 else (if x<3174 then 2 else 3))) else (if x<3252 then (if x<3226 then 3 else 1) else (if x<3282 then 0 else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5903 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2652,2668,2674,2702,2730,2740,2758,2776,2792,3118,3130,3158,3164,3174,3192,3214,3226,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5903 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5903 2652 5
  · have he : independentCachedBranchMembers5903.erase 2652=independentCachedBranchMembers5901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5901
  · have he : independentCachedBranchMembers5903.filter (independentCachedEdge 2652)=independentCachedBranchMembers5902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5902
def independentCachedBranchMembers5904 : Finset ℕ := ([1614,1652,1686,1692,1702,1708,1738,1776,2674,2730,2758,3130,3158,3164,3174,3214,3252,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5904 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5904 5 (fun x => (if x<2758 then (if x<1708 then (if x<1686 then (if x<1652 then 0 else 0) else (if x<1692 then 0 else (if x<1702 then 1 else 1))) else (if x<1776 then (if x<1738 then 0 else 1) else (if x<2674 then 1 else (if x<2730 then 2 else 2)))) else (if x<3214 then (if x<3158 then (if x<3130 then 2 else 2) else (if x<3164 then 0 else (if x<3174 then 3 else 3))) else (if x<3282 then (if x<3252 then 0 else 0) else (if x<3298 then 3 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5905 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2618,2652,2668,2674,2702,2730,2740,2758,2776,2792,3118,3130,3158,3164,3174,3192,3214,3226,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5905 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5905 2618 5
  · have he : independentCachedBranchMembers5905.erase 2618=independentCachedBranchMembers5903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5903
  · have he : independentCachedBranchMembers5905.filter (independentCachedEdge 2618)=independentCachedBranchMembers5904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5904
def independentCachedBranchMembers5906 : Finset ℕ := ([1590,1596,1614,1626,1686,1692,1764,1776,2668,2674,2730,2740,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5906 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5906 5 (fun x => (if x<2740 then (if x<1692 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1626 then 0 else (if x<1686 then 1 else 1))) else (if x<2668 then (if x<1764 then 0 else (if x<1776 then 0 else 1)) else (if x<2674 then 2 else (if x<2730 then 2 else 2)))) else (if x<3158 then (if x<2776 then (if x<2758 then 0 else 2) else (if x<3118 then 2 else (if x<3130 then 3 else 4))) else (if x<3226 then (if x<3164 then 3 else (if x<3214 then 4 else 4)) else (if x<3298 then 3 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5907 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2618,2652,2668,2674,2702,2730,2740,2758,2776,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5907 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5907 3242 5
  · have he : independentCachedBranchMembers5907.erase 3242=independentCachedBranchMembers5905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5905
  · have he : independentCachedBranchMembers5907.filter (independentCachedEdge 3242)=independentCachedBranchMembers5906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5906
def independentCachedBranchMembers5908 : Finset ℕ := ([1590,1614,1626,1652,1686,1708,1720,1748,2652,2674,2730,2758,2792,3118,3130,3158,3192,3214,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5908 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5908 5 (fun x => (if x<2758 then (if x<1708 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else (if x<1686 then 1 else 1))) else (if x<2652 then (if x<1720 then 0 else (if x<1748 then 1 else 0)) else (if x<2674 then 2 else (if x<2730 then 2 else 3)))) else (if x<3192 then (if x<3118 then (if x<2792 then 2 else 2) else (if x<3130 then 0 else (if x<3158 then 3 else 0))) else (if x<3252 then (if x<3214 then 1 else (if x<3226 then 3 else 1)) else (if x<3276 then 0 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5909 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2618,2652,2668,2674,2702,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5909 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5909 2786 5
  · have he : independentCachedBranchMembers5909.erase 2786=independentCachedBranchMembers5907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5907
  · have he : independentCachedBranchMembers5909.filter (independentCachedEdge 2786)=independentCachedBranchMembers5908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5908
def independentCachedBranchMembers5910 : Finset ℕ := ([1590,1596,1614,1642,1702,1708,1748,1776,2618,2668,2702,2730,2776,3118,3158,3164,3192,3226,3252,3276,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5910 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5910 5 (fun x => (if x<2730 then (if x<1708 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1642 then 0 else (if x<1702 then 1 else 1))) else (if x<2618 then (if x<1748 then 0 else (if x<1776 then 0 else 1)) else (if x<2668 then 2 else (if x<2702 then 2 else 2)))) else (if x<3192 then (if x<3118 then (if x<2776 then 3 else 2) else (if x<3158 then 0 else (if x<3164 then 0 else 3))) else (if x<3276 then (if x<3226 then 1 else (if x<3252 then 2 else 0)) else (if x<3298 then 0 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5911 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2618,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5911 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5911 2714 5
  · have he : independentCachedBranchMembers5911.erase 2714=independentCachedBranchMembers5909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5909
  · have he : independentCachedBranchMembers5911.filter (independentCachedEdge 2714)=independentCachedBranchMembers5910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5910
def independentCachedBranchMembers5912 : Finset ℕ := ([1596,1642,1692,1702,1714,1738,1764,1776,2652,2674,2730,2758,2792,3118,3130,3158,3192,3214,3226,3252,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5912 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5912 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5912 5 (fun x => (if x<2758 then (if x<1738 then (if x<1692 then (if x<1642 then 0 else 0) else (if x<1702 then 1 else (if x<1714 then 0 else 1))) else (if x<2652 then (if x<1764 then 1 else (if x<1776 then 1 else 0)) else (if x<2674 then 2 else (if x<2730 then 2 else 3)))) else (if x<3192 then (if x<3118 then (if x<2792 then 2 else 2) else (if x<3130 then 0 else (if x<3158 then 3 else 2))) else (if x<3252 then (if x<3214 then 0 else (if x<3226 then 3 else 1)) else (if x<3276 then 0 else (if x<3298 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5913 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5913 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5913 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5913 2646 5
  · have he : independentCachedBranchMembers5913.erase 2646=independentCachedBranchMembers5911 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5911
  · have he : independentCachedBranchMembers5913.filter (independentCachedEdge 2646)=independentCachedBranchMembers5912 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5912
def independentCachedBranchMembers5914 : Finset ℕ := ([1626,1652,1686,1692,1714,1720,1738,1764,2618,2668,2702,2730,2776,3118,3158,3164,3192,3226,3252,3276,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5914 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5914 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5914 5 (fun x => (if x<2730 then (if x<1720 then (if x<1686 then (if x<1652 then 0 else 0) else (if x<1692 then 0 else (if x<1714 then 1 else 1))) else (if x<2618 then (if x<1738 then 0 else (if x<1764 then 1 else 1)) else (if x<2668 then 2 else (if x<2702 then 2 else 2)))) else (if x<3192 then (if x<3118 then (if x<2776 then 3 else 2) else (if x<3158 then 2 else (if x<3164 then 0 else 3))) else (if x<3276 then (if x<3226 then 0 else (if x<3252 then 0 else 0)) else (if x<3298 then 1 else (if x<3304 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5915 : Finset ℕ := ([1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5915 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5915 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5915 2606 5
  · have he : independentCachedBranchMembers5915.erase 2606=independentCachedBranchMembers5913 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5913
  · have he : independentCachedBranchMembers5915.filter (independentCachedEdge 2606)=independentCachedBranchMembers5914 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5914
def independentCachedBranchMembers5916 : Finset ℕ := ([1596,1614,1652,1686,1692,1702,1708,1748,2606,2646,2652,2668,2702,2740,2758,3118,3158,3164,3174,3214,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5916 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5916 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5916 5 (fun x => (if x<2668 then (if x<1702 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1686 then 1 else (if x<1692 then 0 else 1))) else (if x<2606 then (if x<1708 then 1 else (if x<1748 then 2 else 2)) else (if x<2646 then 2 else (if x<2652 then 2 else 1)))) else (if x<3158 then (if x<2740 then (if x<2702 then 0 else 1) else (if x<2758 then 0 else (if x<3118 then 0 else 3))) else (if x<3214 then (if x<3164 then 3 else (if x<3174 then 4 else 4)) else (if x<3252 then 4 else (if x<3276 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5917 : Finset ℕ := ([1596,1652,1686,1702,2652,2668,2702,2758,3164,3214] : List ℕ).toFinset
theorem independentCachedBranchBound5917 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5917 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5917 4 (fun x => (if x<2668 then (if x<1686 then (if x<1652 then 0 else 1) else (if x<1702 then 0 else (if x<2652 then 1 else 1))) else (if x<2758 then (if x<2702 then 0 else 1) else (if x<3164 then 0 else (if x<3214 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5918 : Finset ℕ := ([1590,1596,1614,1652,1686,1692,1702,1708,1748,2606,2646,2652,2668,2702,2740,2758,3118,3158,3164,3174,3214,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5918 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5918 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5918 1590 4
  · have he : independentCachedBranchMembers5918.erase 1590=independentCachedBranchMembers5916 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5916
  · have he : independentCachedBranchMembers5918.filter (independentCachedEdge 1590)=independentCachedBranchMembers5917 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5917
def independentCachedBranchMembers5919 : Finset ℕ := ([1652,1702,1708,1748,2606,2646,2652,2702,3118,3158,3164,3214] : List ℕ).toFinset
theorem independentCachedBranchBound5919 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5919 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5919 4 (fun x => (if x<2652 then (if x<1748 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<2606 then 1 else (if x<2646 then 1 else 1))) else (if x<3158 then (if x<2702 then 0 else (if x<3118 then 0 else 2)) else (if x<3164 then 2 else (if x<3214 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
