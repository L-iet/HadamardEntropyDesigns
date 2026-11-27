/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch126
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6848 : Finset ℕ := ([36,48,130,192,1590,1644,1734,1738,2614,2668,2680,2716,2758,2762,2770,3132,3174,3222,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6848 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6848 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6848 5 (fun x => (if x<2680 then (if x<1644 then (if x<130 then (if x<48 then 0 else 1) else (if x<192 then 0 else (if x<1590 then 1 else 1))) else (if x<1738 then (if x<1734 then 0 else 1) else (if x<2614 then 0 else (if x<2668 then 2 else 2)))) else (if x<3132 then (if x<2758 then (if x<2716 then 3 else 2) else (if x<2762 then 2 else (if x<2770 then 1 else 0))) else (if x<3222 then (if x<3174 then 0 else 2) else (if x<3276 then 2 else (if x<3288 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6849 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2668,2680,2702,2714,2716,2758,2762,2770,2776,3118,3130,3132,3174,3188,3192,3222,3228,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6849 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6849 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6849 3228 5
  · have he : independentCachedBranchMembers6849.erase 3228=independentCachedBranchMembers6847 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6847
  · have he : independentCachedBranchMembers6849.filter (independentCachedEdge 3228)=independentCachedBranchMembers6848 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6848
def independentCachedBranchMembers6850 : Finset ℕ := ([36,48,130,136,1590,1596,1644,1650,1678,1690,1738,1748,2716,2758,2770,2776,3132,3174,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6850 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6850 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6850 5 (fun x => (if x<1738 then (if x<1596 then (if x<130 then (if x<48 then 0 else 1) else (if x<136 then 0 else (if x<1590 then 1 else 1))) else (if x<1650 then (if x<1644 then 0 else 2) else (if x<1678 then 2 else (if x<1690 then 1 else 0)))) else (if x<2776 then (if x<2716 then (if x<1748 then 2 else 2) else (if x<2758 then 3 else (if x<2770 then 3 else 0))) else (if x<3174 then (if x<3132 then 4 else 3) else (if x<3192 then 3 else (if x<3274 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6851 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3228,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6851 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6851 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6851 2772 5
  · have he : independentCachedBranchMembers6851.erase 2772=independentCachedBranchMembers6849 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6849
  · have he : independentCachedBranchMembers6851.filter (independentCachedEdge 2772)=independentCachedBranchMembers6850 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6850
def independentCachedBranchMembers6852 : Finset ℕ := ([136,222,1596,1650,1678,1690,1748,1752,2614,2668,2680,2716,2758,2762,2770,3132,3174,3222,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6852 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6852 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6852 5 (fun x => (if x<2680 then (if x<1690 then (if x<1596 then (if x<222 then 0 else 0) else (if x<1650 then 1 else (if x<1678 then 1 else 0))) else (if x<1752 then (if x<1748 then 1 else 1) else (if x<2614 then 0 else (if x<2668 then 2 else 2)))) else (if x<3132 then (if x<2758 then (if x<2716 then 3 else 0) else (if x<2762 then 2 else (if x<2770 then 0 else 1))) else (if x<3222 then (if x<3174 then 2 else 2) else (if x<3276 then 2 else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6853 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2620,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3228,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6853 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6853 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6853 2620 5
  · have he : independentCachedBranchMembers6853.erase 2620=independentCachedBranchMembers6851 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6851
  · have he : independentCachedBranchMembers6853.filter (independentCachedEdge 2620)=independentCachedBranchMembers6852 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6852
def independentCachedBranchMembers6854 : Finset ℕ := ([36,136,1590,1644,1650,1690,1734,1752,2614,2668,2714,2716,2758,2776,3130,3132,3174,3192,3222,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6854 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6854 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6854 5 (fun x => (if x<2716 then (if x<1690 then (if x<1590 then (if x<136 then 0 else 0) else (if x<1644 then 0 else (if x<1650 then 1 else 1))) else (if x<2614 then (if x<1734 then 0 else (if x<1752 then 1 else 1)) else (if x<2668 then 2 else (if x<2714 then 2 else 3)))) else (if x<3174 then (if x<2776 then (if x<2758 then 2 else 2) else (if x<3130 then 0 else (if x<3132 then 3 else 2))) else (if x<3274 then (if x<3192 then 0 else (if x<3222 then 1 else 2)) else (if x<3276 then 0 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6855 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2620,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6855 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6855 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6855 3270 5
  · have he : independentCachedBranchMembers6855.erase 3270=independentCachedBranchMembers6853 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6853
  · have he : independentCachedBranchMembers6855.filter (independentCachedEdge 3270)=independentCachedBranchMembers6854 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6854
def independentCachedBranchMembers6856 : Finset ℕ := ([48,192,1590,1596,1650,1690,1734,1748,2614,2620,2680,2714,2758,2772,3130,3174,3188,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6856 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6856 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6856 5 (fun x => (if x<2714 then (if x<1690 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1596 then 0 else (if x<1650 then 1 else 1))) else (if x<2614 then (if x<1734 then 1 else (if x<1748 then 0 else 1)) else (if x<2620 then 2 else (if x<2680 then 0 else 2)))) else (if x<3188 then (if x<2772 then (if x<2758 then 2 else 3) else (if x<3130 then 2 else (if x<3174 then 0 else 3))) else (if x<3274 then (if x<3222 then 1 else (if x<3228 then 2 else 1)) else (if x<3282 then 0 else (if x<3288 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6857 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2620,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6857 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6857 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6857 3226 5
  · have he : independentCachedBranchMembers6857.erase 3226=independentCachedBranchMembers6855 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6855
  · have he : independentCachedBranchMembers6857.filter (independentCachedEdge 3226)=independentCachedBranchMembers6856 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6856
def independentCachedBranchMembers6858 : Finset ℕ := ([48,130,192,222,1596,1678,1738,1748,2614,2668,2714,2716,2758,2776,3130,3132,3174,3192,3222,3274,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6858 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6858 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6858 5 (fun x => (if x<2716 then (if x<1678 then (if x<192 then (if x<130 then 0 else 0) else (if x<222 then 1 else (if x<1596 then 1 else 0))) else (if x<2614 then (if x<1738 then 0 else (if x<1748 then 1 else 1)) else (if x<2668 then 2 else (if x<2714 then 2 else 3)))) else (if x<3174 then (if x<2776 then (if x<2758 then 2 else 0) else (if x<3130 then 1 else (if x<3132 then 3 else 2))) else (if x<3274 then (if x<3192 then 2 else (if x<3222 then 0 else 2)) else (if x<3276 then 0 else (if x<3282 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6859 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6859 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6859 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6859 2662 5
  · have he : independentCachedBranchMembers6859.erase 2662=independentCachedBranchMembers6857 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6857
  · have he : independentCachedBranchMembers6859.filter (independentCachedEdge 2662)=independentCachedBranchMembers6858 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6858
def independentCachedBranchMembers6860 : Finset ℕ := ([36,130,136,222,1644,1678,1738,1752,2614,2620,2680,2714,2758,2772,3130,3174,3188,3222,3228,3274,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6860 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6860 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6860 5 (fun x => (if x<2714 then (if x<1678 then (if x<136 then (if x<130 then 0 else 0) else (if x<222 then 1 else (if x<1644 then 1 else 0))) else (if x<2614 then (if x<1738 then 1 else (if x<1752 then 0 else 1)) else (if x<2620 then 2 else (if x<2680 then 0 else 2)))) else (if x<3188 then (if x<2772 then (if x<2758 then 0 else 3) else (if x<3130 then 2 else (if x<3174 then 2 else 3))) else (if x<3274 then (if x<3222 then 0 else (if x<3228 then 2 else 1)) else (if x<3282 then 1 else (if x<3288 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6861 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6861 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6861 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6861 2618 5
  · have he : independentCachedBranchMembers6861.erase 2618=independentCachedBranchMembers6859 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6859
  · have he : independentCachedBranchMembers6861.filter (independentCachedEdge 2618)=independentCachedBranchMembers6860 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6860
def independentCachedBranchMembers6862 : Finset ℕ := ([48,136,1596,1644,1650,1690,1734,1738,1748,1752,2614,2618,2662,2680,2702,2716,2770,3130,3174,3188,3192,3228,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6862 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6862 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6862 5 (fun x => (if x<2662 then (if x<1734 then (if x<1644 then (if x<136 then 0 else (if x<1596 then 0 else 1)) else (if x<1650 then 2 else (if x<1690 then 0 else 1))) else (if x<1752 then (if x<1738 then 2 else (if x<1748 then 0 else 1)) else (if x<2614 then 2 else (if x<2618 then 0 else 1)))) else (if x<3174 then (if x<2716 then (if x<2680 then 2 else (if x<2702 then 2 else 0)) else (if x<2770 then 1 else (if x<3130 then 1 else 3))) else (if x<3228 then (if x<3188 then 3 else (if x<3192 then 0 else 4)) else (if x<3276 then 4 else (if x<3282 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6863 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6863 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6863 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6863 1746 5
  · have he : independentCachedBranchMembers6863.erase 1746=independentCachedBranchMembers6861 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6861
  · have he : independentCachedBranchMembers6863.filter (independentCachedEdge 1746)=independentCachedBranchMembers6862 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6862
def independentCachedBranchMembers6864 : Finset ℕ := ([36,130,1590,1644,1650,1678,1734,1738,1748,1752,2620,2662,2680,2714,2770,3118,3132,3174,3188,3192,3222,3226,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound6864 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6864 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6864 5 (fun x => (if x<2680 then (if x<1734 then (if x<1644 then (if x<130 then 0 else (if x<1590 then 0 else 1)) else (if x<1650 then 0 else (if x<1678 then 2 else 1))) else (if x<1752 then (if x<1738 then 2 else (if x<1748 then 0 else 1)) else (if x<2620 then 2 else (if x<2662 then 0 else 2)))) else (if x<3188 then (if x<3118 then (if x<2714 then 2 else (if x<2770 then 0 else 2)) else (if x<3132 then 1 else (if x<3174 then 3 else 3))) else (if x<3226 then (if x<3192 then 0 else (if x<3222 then 4 else 1)) else (if x<3276 then 4 else (if x<3282 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6865 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1678,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6865 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6865 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6865 1740 5
  · have he : independentCachedBranchMembers6865.erase 1740=independentCachedBranchMembers6863 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6863
  · have he : independentCachedBranchMembers6865.filter (independentCachedEdge 1740)=independentCachedBranchMembers6864 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6864
def independentCachedBranchMembers6866 : Finset ℕ := ([192,222,1590,1596,1644,1650,1678,1690,1738,1748,2618,2716,2758,2770,2776,3118,3130,3188,3222,3228,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6866 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6866 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6866 5 (fun x => (if x<2758 then (if x<1678 then (if x<1596 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1644 then 2 else (if x<1650 then 1 else 2))) else (if x<1748 then (if x<1690 then 1 else (if x<1738 then 2 else 0)) else (if x<2618 then 0 else (if x<2716 then 2 else 2)))) else (if x<3222 then (if x<3118 then (if x<2770 then 0 else (if x<2776 then 2 else 0)) else (if x<3130 then 1 else (if x<3188 then 3 else 1))) else (if x<3276 then (if x<3228 then 1 else (if x<3270 then 3 else 4)) else (if x<3282 then 0 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6867 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1644,1650,1652,1678,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6867 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6867 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6867 1652 5
  · have he : independentCachedBranchMembers6867.erase 1652=independentCachedBranchMembers6865 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6865
  · have he : independentCachedBranchMembers6867.filter (independentCachedEdge 1652)=independentCachedBranchMembers6866 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6866
def independentCachedBranchMembers6868 : Finset ℕ := ([36,48,130,136,192,222,1644,1650,1738,1748,2614,2620,2702,2714,2758,2770,2776,3132,3188,3226,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6868 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6868 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6868 5 (fun x => (if x<2702 then (if x<1644 then (if x<136 then (if x<48 then 0 else (if x<130 then 1 else 0)) else (if x<192 then 1 else (if x<222 then 2 else 2))) else (if x<1748 then (if x<1650 then 0 else (if x<1738 then 1 else 0)) else (if x<2614 then 2 else (if x<2620 then 1 else 0)))) else (if x<3188 then (if x<2770 then (if x<2714 then 1 else (if x<2758 then 0 else 2)) else (if x<2776 then 3 else (if x<3132 then 2 else 3))) else (if x<3276 then (if x<3226 then 0 else (if x<3270 then 3 else 4)) else (if x<3282 then 1 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6869 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1642,1644,1650,1652,1678,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6869 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6869 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6869 1642 5
  · have he : independentCachedBranchMembers6869.erase 1642=independentCachedBranchMembers6867 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6867
  · have he : independentCachedBranchMembers6869.filter (independentCachedEdge 1642)=independentCachedBranchMembers6868 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6868
def independentCachedBranchMembers6870 : Finset ℕ := ([36,192,1590,1642,1644,1690,1734,1746,1748,2618,2620,2662,2762,2776,3118,3130,3132,3174,3188,3222,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6870 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6870 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6870 5 (fun x => (if x<2662 then (if x<1690 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1642 then 0 else (if x<1644 then 1 else 2))) else (if x<1748 then (if x<1734 then 1 else (if x<1746 then 1 else 0)) else (if x<2618 then 2 else (if x<2620 then 1 else 0)))) else (if x<3174 then (if x<3118 then (if x<2762 then 1 else (if x<2776 then 1 else 0)) else (if x<3130 then 0 else (if x<3132 then 3 else 4))) else (if x<3274 then (if x<3188 then 3 else (if x<3222 then 2 else 2)) else (if x<3276 then 0 else (if x<3288 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6871 : Finset ℕ := ([36,192,1690,1734,2618,2620,2662,2776,3130,3132,3174,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6871 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6871 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6871 4 (fun x => (if x<2662 then (if x<1734 then (if x<192 then 0 else (if x<1690 then 0 else 1)) else (if x<2618 then 1 else (if x<2620 then 1 else 0))) else (if x<3132 then (if x<2776 then 1 else (if x<3130 then 0 else 2)) else (if x<3174 then 3 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6872 : Finset ℕ := ([36,192,1590,1642,1644,1678,1690,1734,1746,1748,2618,2620,2662,2762,2776,3118,3130,3132,3174,3188,3222,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6872 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6872 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6872 1678 4
  · have he : independentCachedBranchMembers6872.erase 1678=independentCachedBranchMembers6870 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6870
  · have he : independentCachedBranchMembers6872.filter (independentCachedEdge 1678)=independentCachedBranchMembers6871 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6871
def independentCachedBranchMembers6873 : Finset ℕ := ([192,1642,1644,1734,1746,1748,2618,2620,3118,3130,3132,3222] : List ℕ).toFinset
theorem independentCachedBranchBound6873 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6873 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6873 4 (fun x => (if x<2618 then (if x<1734 then (if x<1642 then 0 else (if x<1644 then 1 else 2)) else (if x<1746 then 0 else (if x<1748 then 1 else 2))) else (if x<3130 then (if x<2620 then 0 else (if x<3118 then 3 else 1)) else (if x<3132 then 3 else (if x<3222 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6874 : Finset ℕ := ([36,136,192,1590,1642,1644,1678,1690,1734,1746,1748,2618,2620,2662,2762,2776,3118,3130,3132,3174,3188,3222,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6874 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6874 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6874 136 4
  · have he : independentCachedBranchMembers6874.erase 136=independentCachedBranchMembers6872 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6872
  · have he : independentCachedBranchMembers6874.filter (independentCachedEdge 136)=independentCachedBranchMembers6873 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6873
def independentCachedBranchMembers6875 : Finset ℕ := ([36,1642,1644,1690,1746,1748,2662,2776,3118,3174,3222,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6875 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6875 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6875 4 (fun x => (if x<2662 then (if x<1690 then (if x<1642 then 0 else (if x<1644 then 1 else 0)) else (if x<1746 then 1 else (if x<1748 then 2 else 3))) else (if x<3174 then (if x<2776 then 0 else (if x<3118 then 2 else 0)) else (if x<3222 then 1 else (if x<3288 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6876 : Finset ℕ := ([36,48,136,192,1590,1642,1644,1678,1690,1734,1746,1748,2618,2620,2662,2762,2776,3118,3130,3132,3174,3188,3222,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6876 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6876 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6876 48 4
  · have he : independentCachedBranchMembers6876.erase 48=independentCachedBranchMembers6874 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6874
  · have he : independentCachedBranchMembers6876.filter (independentCachedEdge 48)=independentCachedBranchMembers6875 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6875
def independentCachedBranchMembers6877 : Finset ℕ := ([36,48,130,136,192,222,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6877 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6877 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6877 1686 5
  · have he : independentCachedBranchMembers6877.erase 1686=independentCachedBranchMembers6869 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6869
  · have he : independentCachedBranchMembers6877.filter (independentCachedEdge 1686)=independentCachedBranchMembers6876 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6876
def independentCachedBranchMembers6878 : Finset ℕ := ([130,222,1596,1642,1644,1678,1746,1748,1752,2680,2714,2716,2758,2762,3118,3188,3192,3222,3226,3228,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6878 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6878 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6878 5 (fun x => (if x<2716 then (if x<1678 then (if x<1596 then (if x<222 then 0 else 0) else (if x<1642 then 1 else (if x<1644 then 1 else 2))) else (if x<1752 then (if x<1746 then 0 else (if x<1748 then 0 else 2)) else (if x<2680 then 1 else (if x<2714 then 1 else 0)))) else (if x<3222 then (if x<3118 then (if x<2758 then 1 else (if x<2762 then 0 else 1)) else (if x<3188 then 2 else (if x<3192 then 2 else 3))) else (if x<3270 then (if x<3226 then 0 else (if x<3228 then 3 else 4)) else (if x<3274 then 4 else (if x<3276 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6879 : Finset ℕ := ([130,222,1596,1752,2680,2714,2716,2758,3192,3226,3228,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6879 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6879 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6879 4 (fun x => (if x<2716 then (if x<1752 then (if x<222 then 0 else (if x<1596 then 0 else 1)) else (if x<2680 then 1 else (if x<2714 then 1 else 0))) else (if x<3226 then (if x<2758 then 1 else (if x<3192 then 0 else 2)) else (if x<3228 then 2 else (if x<3270 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
