/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch127
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6880 : Finset ℕ := ([130,222,1590,1596,1642,1644,1678,1746,1748,1752,2680,2714,2716,2758,2762,3118,3188,3192,3222,3226,3228,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6880 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6880 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6880 1590 4
  · have he : independentCachedBranchMembers6880.erase 1590=independentCachedBranchMembers6878 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6878
  · have he : independentCachedBranchMembers6880.filter (independentCachedEdge 1590)=independentCachedBranchMembers6879 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6879
def independentCachedBranchMembers6881 : Finset ℕ := ([130,1596,1642,1644,1746,1748,2680,2758,3118,3192,3222,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6881 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6881 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6881 4 (fun x => (if x<2680 then (if x<1644 then (if x<1596 then 0 else (if x<1642 then 0 else 1)) else (if x<1746 then 2 else (if x<1748 then 1 else 2))) else (if x<3192 then (if x<2758 then 0 else (if x<3118 then 3 else 1)) else (if x<3222 then 3 else (if x<3270 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6882 : Finset ℕ := ([130,136,222,1590,1596,1642,1644,1678,1746,1748,1752,2680,2714,2716,2758,2762,3118,3188,3192,3222,3226,3228,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6882 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6882 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6882 136 4
  · have he : independentCachedBranchMembers6882.erase 136=independentCachedBranchMembers6880 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6880
  · have he : independentCachedBranchMembers6882.filter (independentCachedEdge 136)=independentCachedBranchMembers6881 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6881
def independentCachedBranchMembers6883 : Finset ℕ := ([222,1644,1746,1748,1752,2714,2716,3118,3222,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6883 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6883 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6883 4 (fun x => (if x<2714 then (if x<1746 then (if x<1644 then 0 else 1) else (if x<1748 then 0 else (if x<1752 then 1 else 2))) else (if x<3222 then (if x<2716 then 0 else (if x<3118 then 2 else 1)) else (if x<3226 then 0 else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6884 : Finset ℕ := ([222,1644,1748,2714,3226] : List ℕ).toFinset
theorem independentCachedBranchBound6884 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6884 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6884 3 (fun x => (if x<1748 then (if x<1644 then 0 else 1) else (if x<2714 then 0 else (if x<3226 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6885 : Finset ℕ := ([222,1642,1644,1746,1748,1752,2714,2716,3118,3222,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6885 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6885 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6885 1642 3
  · have he : independentCachedBranchMembers6885.erase 1642=independentCachedBranchMembers6883 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6883
  · have he : independentCachedBranchMembers6885.filter (independentCachedEdge 1642)=independentCachedBranchMembers6884 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6884
def independentCachedBranchMembers6886 : Finset ℕ := ([48,130,136,222,1590,1596,1642,1644,1678,1746,1748,1752,2680,2714,2716,2758,2762,3118,3188,3192,3222,3226,3228,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6886 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6886 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6886 48 4
  · have he : independentCachedBranchMembers6886.erase 48=independentCachedBranchMembers6882 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6882
  · have he : independentCachedBranchMembers6886.filter (independentCachedEdge 48)=independentCachedBranchMembers6885 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6885
def independentCachedBranchMembers6887 : Finset ℕ := ([36,48,130,136,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6887 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6887 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6887 1582 5
  · have he : independentCachedBranchMembers6887.erase 1582=independentCachedBranchMembers6877 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6877
  · have he : independentCachedBranchMembers6887.filter (independentCachedEdge 1582)=independentCachedBranchMembers6886 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6886
def independentCachedBranchMembers6888 : Finset ℕ := ([48,130,192,1596,1652,1734,1740,2614,2618,2620,2680,2702,2758,2762,3130,3132,3188,3192,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6888 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6888 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6888 5 (fun x => (if x<2680 then (if x<1734 then (if x<192 then (if x<130 then 0 else 0) else (if x<1596 then 1 else (if x<1652 then 0 else 2))) else (if x<2614 then (if x<1740 then 1 else 2) else (if x<2618 then 2 else (if x<2620 then 1 else 3)))) else (if x<3132 then (if x<2758 then (if x<2702 then 0 else 2) else (if x<2762 then 4 else (if x<3130 then 0 else 3))) else (if x<3270 then (if x<3188 then 1 else (if x<3192 then 0 else 4)) else (if x<3274 then 0 else (if x<3276 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6889 : Finset ℕ := ([1596,1652,1734,1740,2618,2680,2762,3130,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6889 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6889 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6889 4 (fun x => (if x<2680 then (if x<1734 then (if x<1652 then 0 else 1) else (if x<1740 then 1 else (if x<2618 then 0 else 0))) else (if x<3130 then (if x<2762 then 1 else 0) else (if x<3192 then 2 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6890 : Finset ℕ := ([48,130,192,1596,1652,1734,1738,1740,2614,2618,2620,2680,2702,2758,2762,3130,3132,3188,3192,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6890 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6890 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6890 1738 4
  · have he : independentCachedBranchMembers6890.erase 1738=independentCachedBranchMembers6888 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6888
  · have he : independentCachedBranchMembers6890.filter (independentCachedEdge 1738)=independentCachedBranchMembers6889 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6889
def independentCachedBranchMembers6891 : Finset ℕ := ([130,192,1652,1740,2620,2758,2762,3132,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound6891 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6891 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6891 4 (fun x => (if x<2758 then (if x<1652 then (if x<192 then 0 else 1) else (if x<1740 then 0 else (if x<2620 then 1 else 0))) else (if x<3132 then (if x<2762 then 1 else 2) else (if x<3270 then 2 else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6892 : Finset ℕ := ([48,130,192,1596,1650,1652,1734,1738,1740,2614,2618,2620,2680,2702,2758,2762,3130,3132,3188,3192,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6892 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6892 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6892 1650 4
  · have he : independentCachedBranchMembers6892.erase 1650=independentCachedBranchMembers6890 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6890
  · have he : independentCachedBranchMembers6892.filter (independentCachedEdge 1650)=independentCachedBranchMembers6891 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6891
def independentCachedBranchMembers6893 : Finset ℕ := ([192,1650,1652,1734,1738,1740,2614,2618,2620,2702,3130,3132] : List ℕ).toFinset
theorem independentCachedBranchBound6893 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6893 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6893 4 (fun x => (if x<2614 then (if x<1734 then (if x<1650 then 0 else (if x<1652 then 1 else 2)) else (if x<1738 then 0 else (if x<1740 then 1 else 2))) else (if x<2702 then (if x<2618 then 1 else (if x<2620 then 0 else 3)) else (if x<3130 then 1 else (if x<3132 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6894 : Finset ℕ := ([48,130,192,1596,1650,1652,1678,1734,1738,1740,2614,2618,2620,2680,2702,2758,2762,3130,3132,3188,3192,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6894 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6894 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6894 1678 4
  · have he : independentCachedBranchMembers6894.erase 1678=independentCachedBranchMembers6892 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6892
  · have he : independentCachedBranchMembers6894.filter (independentCachedEdge 1678)=independentCachedBranchMembers6893 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6893
def independentCachedBranchMembers6895 : Finset ℕ := ([130,1596,1650,1652,1738,1740,2614,2680,2702,2758,3192,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6895 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6895 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6895 4 (fun x => (if x<2614 then (if x<1652 then (if x<1596 then 0 else (if x<1650 then 0 else 1)) else (if x<1738 then 2 else (if x<1740 then 1 else 2))) else (if x<2758 then (if x<2680 then 1 else (if x<2702 then 0 else 1)) else (if x<3192 then 3 else (if x<3270 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6896 : Finset ℕ := ([48,130,192,1590,1596,1650,1652,1678,1734,1738,1740,2614,2618,2620,2680,2702,2758,2762,3130,3132,3188,3192,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6896 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6896 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6896 1590 4
  · have he : independentCachedBranchMembers6896.erase 1590=independentCachedBranchMembers6894 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6894
  · have he : independentCachedBranchMembers6896.filter (independentCachedEdge 1590)=independentCachedBranchMembers6895 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6895
def independentCachedBranchMembers6897 : Finset ℕ := ([130,192,1596,1734,2618,2620,2680,2758,3130,3132,3192,3270] : List ℕ).toFinset
theorem independentCachedBranchBound6897 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6897 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6897 4 (fun x => (if x<2680 then (if x<1734 then (if x<192 then 0 else (if x<1596 then 1 else 0)) else (if x<2618 then 1 else (if x<2620 then 1 else 2))) else (if x<3132 then (if x<2758 then 0 else (if x<3130 then 3 else 2)) else (if x<3192 then 1 else (if x<3270 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6898 : Finset ℕ := ([48,130,136,192,1590,1596,1650,1652,1678,1734,1738,1740,2614,2618,2620,2680,2702,2758,2762,3130,3132,3188,3192,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6898 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6898 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6898 136 4
  · have he : independentCachedBranchMembers6898.erase 136=independentCachedBranchMembers6896 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6896
  · have he : independentCachedBranchMembers6898.filter (independentCachedEdge 136)=independentCachedBranchMembers6897 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6897
def independentCachedBranchMembers6899 : Finset ℕ := ([36,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6899 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6899 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6899 144 5
  · have he : independentCachedBranchMembers6899.erase 144=independentCachedBranchMembers6887 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6887
  · have he : independentCachedBranchMembers6899.filter (independentCachedEdge 144)=independentCachedBranchMembers6898 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6898
def independentCachedBranchMembers6900 : Finset ℕ := ([36,136,222,1650,1652,1678,1690,1738,1740,1752,2614,2662,2702,2714,2716,2762,2776,3174,3188,3226,3228,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6900 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6900 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6900 5 (fun x => (if x<2702 then (if x<1690 then (if x<1650 then (if x<136 then 0 else (if x<222 then 0 else 1)) else (if x<1652 then 2 else (if x<1678 then 0 else 1))) else (if x<1752 then (if x<1738 then 2 else (if x<1740 then 3 else 4)) else (if x<2614 then 0 else (if x<2662 then 0 else 2)))) else (if x<3188 then (if x<2762 then (if x<2714 then 2 else (if x<2716 then 0 else 1)) else (if x<2776 then 1 else (if x<3174 then 3 else 0))) else (if x<3274 then (if x<3226 then 2 else (if x<3228 then 1 else 2)) else (if x<3276 then 0 else (if x<3288 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6901 : Finset ℕ := ([222,1650,1652,1738,1740,1752,2614,2702,2714,2716,3226,3228] : List ℕ).toFinset
theorem independentCachedBranchBound6901 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6901 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6901 4 (fun x => (if x<2614 then (if x<1738 then (if x<1650 then 0 else (if x<1652 then 1 else 2)) else (if x<1740 then 0 else (if x<1752 then 2 else 1))) else (if x<2716 then (if x<2702 then 1 else (if x<2714 then 0 else 3)) else (if x<3226 then 1 else (if x<3228 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6902 : Finset ℕ := ([36,136,222,1590,1650,1652,1678,1690,1738,1740,1752,2614,2662,2702,2714,2716,2762,2776,3174,3188,3226,3228,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6902 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6902 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6902 1590 4
  · have he : independentCachedBranchMembers6902.erase 1590=independentCachedBranchMembers6900 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6900
  · have he : independentCachedBranchMembers6902.filter (independentCachedEdge 1590)=independentCachedBranchMembers6901 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6901
def independentCachedBranchMembers6903 : Finset ℕ := ([36,222,1690,1752,2662,2714,2716,2776,3174,3226,3228,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6903 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6903 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6903 4 (fun x => (if x<2716 then (if x<1752 then (if x<222 then 0 else (if x<1690 then 1 else 0)) else (if x<2662 then 1 else (if x<2714 then 0 else 1))) else (if x<3226 then (if x<2776 then 2 else (if x<3174 then 3 else 2)) else (if x<3228 then 3 else (if x<3288 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6904 : Finset ℕ := ([36,48,136,222,1590,1650,1652,1678,1690,1738,1740,1752,2614,2662,2702,2714,2716,2762,2776,3174,3188,3226,3228,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6904 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6904 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6904 48 4
  · have he : independentCachedBranchMembers6904.erase 48=independentCachedBranchMembers6902 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6902
  · have he : independentCachedBranchMembers6904.filter (independentCachedEdge 48)=independentCachedBranchMembers6903 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6903
def independentCachedBranchMembers6905 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6905 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6905 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6905 40 5
  · have he : independentCachedBranchMembers6905.erase 40=independentCachedBranchMembers6899 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6899
  · have he : independentCachedBranchMembers6905.filter (independentCachedEdge 40)=independentCachedBranchMembers6904 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6904
def independentCachedBranchMembers6906 : Finset ℕ := ([36,48,130,136,1590,1596,1644,1650,1678,1690,1738,1748,2614,2620,2662,2668,2680,2702,2714,2762,2772,3118,3130,3188,3222,3228,3270,3276,3282,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6906 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6906 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6906 5 (fun x => (if x<2668 then (if x<1650 then (if x<136 then (if x<48 then 0 else (if x<130 then 1 else 0)) else (if x<1596 then (if x<1590 then 1 else 1) else (if x<1644 then 0 else 2))) else (if x<1748 then (if x<1690 then (if x<1678 then 2 else 1) else (if x<1738 then 0 else 2)) else (if x<2620 then (if x<2614 then 2 else 3) else (if x<2662 then 4 else 4)))) else (if x<3130 then (if x<2714 then (if x<2680 then 0 else (if x<2702 then 3 else 4)) else (if x<2772 then (if x<2762 then 3 else 0) else (if x<3118 then 3 else 4))) else (if x<3270 then (if x<3222 then (if x<3188 then 3 else 0) else (if x<3228 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 1) else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6907 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6907 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6907 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6907 3284 5
  · have he : independentCachedBranchMembers6907.erase 3284=independentCachedBranchMembers6905 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6905
  · have he : independentCachedBranchMembers6907.filter (independentCachedEdge 3284)=independentCachedBranchMembers6906 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6906
def independentCachedBranchMembers6908 : Finset ℕ := ([36,40,144,192,1590,1596,1642,1644,1678,1746,1748,1752,2614,2618,2620,2662,2668,2702,2770,2772,2776,3118,3188,3192,3222,3226,3228,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound6908 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6908 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6908 5 (fun x => (if x<2662 then (if x<1644 then (if x<192 then (if x<40 then 0 else (if x<144 then 1 else 0)) else (if x<1596 then (if x<1590 then 1 else 2) else (if x<1642 then 1 else 2))) else (if x<1752 then (if x<1746 then (if x<1678 then 0 else 2) else (if x<1748 then 2 else 1)) else (if x<2618 then (if x<2614 then 0 else 3) else (if x<2620 then 1 else 4)))) else (if x<3188 then (if x<2770 then (if x<2668 then 0 else (if x<2702 then 3 else 3)) else (if x<2776 then (if x<2772 then 0 else 3) else (if x<3118 then 4 else 0))) else (if x<3228 then (if x<3222 then (if x<3192 then 3 else 4) else (if x<3226 then 2 else 0)) else (if x<3274 then (if x<3270 then 4 else 1) else (if x<3276 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6909 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3130,3132,3174,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6909 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6909 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6909 3214 5
  · have he : independentCachedBranchMembers6909.erase 3214=independentCachedBranchMembers6907 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6907
  · have he : independentCachedBranchMembers6909.filter (independentCachedEdge 3214)=independentCachedBranchMembers6908 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6908
def independentCachedBranchMembers6910 : Finset ℕ := ([40,130,144,222,1590,1642,1644,1678,1690,1734,1746,1748,2614,2668,2680,2702,2714,2716,2758,2770,2772,3118,3130,3132,3174,3188,3222,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6910 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6910 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6910 5 (fun x => (if x<2702 then (if x<1678 then (if x<222 then (if x<130 then 0 else (if x<144 then 0 else 1)) else (if x<1642 then (if x<1590 then 1 else 2) else (if x<1644 then 2 else 0))) else (if x<1748 then (if x<1734 then (if x<1690 then 2 else 1) else (if x<1746 then 0 else 2)) else (if x<2668 then (if x<2614 then 1 else 3) else (if x<2680 then 3 else 0)))) else (if x<3130 then (if x<2758 then (if x<2714 then 3 else (if x<2716 then 4 else 1)) else (if x<2772 then (if x<2770 then 4 else 0) else (if x<3118 then 3 else 2))) else (if x<3222 then (if x<3174 then (if x<3132 then 4 else 0) else (if x<3188 then 4 else 3)) else (if x<3276 then (if x<3274 then 0 else 2) else (if x<3288 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6911 : Finset ℕ := ([36,40,48,130,136,144,192,222,1582,1590,1596,1642,1644,1650,1652,1678,1686,1690,1734,1738,1740,1746,1748,1752,2614,2618,2620,2662,2668,2680,2702,2714,2716,2758,2762,2770,2772,2776,3118,3126,3130,3132,3174,3188,3192,3214,3222,3226,3228,3270,3274,3276,3282,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound6911 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6911 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6911 3126 5
  · have he : independentCachedBranchMembers6911.erase 3126=independentCachedBranchMembers6909 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6909
  · have he : independentCachedBranchMembers6911.filter (independentCachedEdge 3126)=independentCachedBranchMembers6910 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6910
end EntropyDesigns.QuadraticRefinement
