/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch165
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8096 : Finset ℕ := ([132,252,1582,1590,1614,1622,1642,1650,1692,1720,1752,1764,2618,2650,2662,2732,2772,2792,2800,3130,3162,3174,3252,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8096 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8096 132 4
  · have he : independentCachedBranchMembers8096.erase 132=independentCachedBranchMembers8094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8094
  · have he : independentCachedBranchMembers8096.filter (independentCachedEdge 132)=independentCachedBranchMembers8095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8095
def independentCachedBranchMembers8097 : Finset ℕ := ([48,72,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8097 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8097 130 5
  · have he : independentCachedBranchMembers8097.erase 130=independentCachedBranchMembers8087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8087
  · have he : independentCachedBranchMembers8097.filter (independentCachedEdge 130)=independentCachedBranchMembers8096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8096
def independentCachedBranchMembers8098 : Finset ℕ := ([1590,1642,1644,1690,1692,1720,1734,1762,1764,2618,2620,2662,2710,2738,2762,2792,3130,3132,3174,3222,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8098 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8098 5 (fun x => (if x<2662 then (if x<1720 then (if x<1644 then (if x<1642 then 0 else 0) else (if x<1690 then 1 else (if x<1692 then 0 else 1))) else (if x<1764 then (if x<1734 then 2 else (if x<1762 then 0 else 2)) else (if x<2618 then 3 else (if x<2620 then 0 else 1)))) else (if x<3132 then (if x<2762 then (if x<2710 then 0 else (if x<2738 then 0 else 2)) else (if x<2792 then 0 else (if x<3130 then 2 else 3))) else (if x<3252 then (if x<3174 then 4 else (if x<3222 then 3 else 4)) else (if x<3276 then 3 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8099 : Finset ℕ := ([1642,1644,1720,1734,2618,2620,2710,2792,3130,3132,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8099 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8099 4 (fun x => (if x<2710 then (if x<1734 then (if x<1644 then 0 else (if x<1720 then 1 else 0)) else (if x<2618 then 1 else (if x<2620 then 0 else 1))) else (if x<3132 then (if x<2792 then 1 else (if x<3130 then 0 else 2)) else (if x<3222 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8100 : Finset ℕ := ([1590,1614,1642,1644,1690,1692,1720,1734,1762,1764,2618,2620,2662,2710,2738,2762,2792,3130,3132,3174,3222,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8100 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8100 1614 4
  · have he : independentCachedBranchMembers8100.erase 1614=independentCachedBranchMembers8098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8098
  · have he : independentCachedBranchMembers8100.filter (independentCachedEdge 1614)=independentCachedBranchMembers8099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8099
def independentCachedBranchMembers8101 : Finset ℕ := ([1692,1720,1734,1762,1764,2618,2620,2662,3130,3132,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8101 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8101 4 (fun x => (if x<2618 then (if x<1734 then (if x<1720 then 0 else 1) else (if x<1762 then 0 else (if x<1764 then 1 else 2))) else (if x<3130 then (if x<2620 then 2 else (if x<2662 then 0 else 0)) else (if x<3132 then 3 else (if x<3174 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8102 : Finset ℕ := ([1692,1720,1764,2620,3132] : List ℕ).toFinset
theorem independentCachedBranchBound8102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8102 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8102 3 (fun x => (if x<1764 then (if x<1720 then 0 else 1) else (if x<2620 then 0 else (if x<3132 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8103 : Finset ℕ := ([1690,1692,1720,1734,1762,1764,2618,2620,2662,3130,3132,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8103 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8103 1690 3
  · have he : independentCachedBranchMembers8103.erase 1690=independentCachedBranchMembers8101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8101
  · have he : independentCachedBranchMembers8103.filter (independentCachedEdge 1690)=independentCachedBranchMembers8102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8102
def independentCachedBranchMembers8104 : Finset ℕ := ([72,1590,1614,1642,1644,1690,1692,1720,1734,1762,1764,2618,2620,2662,2710,2738,2762,2792,3130,3132,3174,3222,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8104 72 4
  · have he : independentCachedBranchMembers8104.erase 72=independentCachedBranchMembers8100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8100
  · have he : independentCachedBranchMembers8104.filter (independentCachedEdge 72)=independentCachedBranchMembers8103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8103
def independentCachedBranchMembers8105 : Finset ℕ := ([1642,1644,1690,1692,1762,1764,2662,2710,2792,3174,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8105 4 (fun x => (if x<2662 then (if x<1692 then (if x<1644 then 0 else (if x<1690 then 1 else 0)) else (if x<1762 then 1 else (if x<1764 then 2 else 3))) else (if x<3174 then (if x<2710 then 0 else (if x<2792 then 0 else 2)) else (if x<3222 then 1 else (if x<3304 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8106 : Finset ℕ := ([48,72,1590,1614,1642,1644,1690,1692,1720,1734,1762,1764,2618,2620,2662,2710,2738,2762,2792,3130,3132,3174,3222,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8106 48 4
  · have he : independentCachedBranchMembers8106.erase 48=independentCachedBranchMembers8104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8104
  · have he : independentCachedBranchMembers8106.filter (independentCachedEdge 48)=independentCachedBranchMembers8105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8105
def independentCachedBranchMembers8107 : Finset ℕ := ([48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8107 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8107 80 5
  · have he : independentCachedBranchMembers8107.erase 80=independentCachedBranchMembers8097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8097
  · have he : independentCachedBranchMembers8107.filter (independentCachedEdge 80)=independentCachedBranchMembers8106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8106
def independentCachedBranchMembers8108 : Finset ℕ := ([1614,1650,1652,1690,1692,1702,1752,1762,1764,2650,2652,2662,2702,2738,2762,2800,3162,3164,3174,3214,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8108 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8108 5 (fun x => (if x<2662 then (if x<1702 then (if x<1652 then (if x<1650 then 0 else 0) else (if x<1690 then 1 else (if x<1692 then 0 else 1))) else (if x<1764 then (if x<1752 then 0 else (if x<1762 then 2 else 2)) else (if x<2650 then 3 else (if x<2652 then 0 else 1)))) else (if x<3164 then (if x<2762 then (if x<2702 then 0 else (if x<2738 then 0 else 0)) else (if x<2800 then 2 else (if x<3162 then 2 else 3))) else (if x<3252 then (if x<3174 then 4 else (if x<3214 then 3 else 4)) else (if x<3276 then 4 else (if x<3312 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8109 : Finset ℕ := ([1650,1652,1702,1752,2650,2652,2702,2800,3162,3164,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8109 4 (fun x => (if x<2702 then (if x<1752 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<2650 then 1 else (if x<2652 then 0 else 1))) else (if x<3164 then (if x<2800 then 0 else (if x<3162 then 1 else 2)) else (if x<3214 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8110 : Finset ℕ := ([1590,1614,1650,1652,1690,1692,1702,1752,1762,1764,2650,2652,2662,2702,2738,2762,2800,3162,3164,3174,3214,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8110 1590 4
  · have he : independentCachedBranchMembers8110.erase 1590=independentCachedBranchMembers8108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8108
  · have he : independentCachedBranchMembers8110.filter (independentCachedEdge 1590)=independentCachedBranchMembers8109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8109
def independentCachedBranchMembers8111 : Finset ℕ := ([1650,1652,1690,1692,1762,1764,2662,2702,2800,3174,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8111 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8111 4 (fun x => (if x<2662 then (if x<1692 then (if x<1652 then 0 else (if x<1690 then 1 else 0)) else (if x<1762 then 1 else (if x<1764 then 2 else 3))) else (if x<3174 then (if x<2702 then 0 else (if x<2800 then 0 else 2)) else (if x<3214 then 1 else (if x<3312 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8112 : Finset ℕ := ([72,1590,1614,1650,1652,1690,1692,1702,1752,1762,1764,2650,2652,2662,2702,2738,2762,2800,3162,3164,3174,3214,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8112 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8112 72 4
  · have he : independentCachedBranchMembers8112.erase 72=independentCachedBranchMembers8110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8110
  · have he : independentCachedBranchMembers8112.filter (independentCachedEdge 72)=independentCachedBranchMembers8111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8111
def independentCachedBranchMembers8113 : Finset ℕ := ([1692,1702,1752,1762,1764,2650,2652,2662,3162,3164,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8113 4 (fun x => (if x<2650 then (if x<1752 then (if x<1702 then 0 else 0) else (if x<1762 then 1 else (if x<1764 then 1 else 2))) else (if x<3162 then (if x<2652 then 2 else (if x<2662 then 0 else 0)) else (if x<3164 then 3 else (if x<3174 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8114 : Finset ℕ := ([1692,1752,1764,2652,3164] : List ℕ).toFinset
theorem independentCachedBranchBound8114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8114 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8114 3 (fun x => (if x<1764 then (if x<1752 then 0 else 1) else (if x<2652 then 0 else (if x<3164 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8115 : Finset ℕ := ([1690,1692,1702,1752,1762,1764,2650,2652,2662,3162,3164,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8115 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8115 1690 3
  · have he : independentCachedBranchMembers8115.erase 1690=independentCachedBranchMembers8113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8113
  · have he : independentCachedBranchMembers8115.filter (independentCachedEdge 1690)=independentCachedBranchMembers8114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8114
def independentCachedBranchMembers8116 : Finset ℕ := ([48,72,1590,1614,1650,1652,1690,1692,1702,1752,1762,1764,2650,2652,2662,2702,2738,2762,2800,3162,3164,3174,3214,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8116 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8116 48 4
  · have he : independentCachedBranchMembers8116.erase 48=independentCachedBranchMembers8112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8112
  · have he : independentCachedBranchMembers8116.filter (independentCachedEdge 48)=independentCachedBranchMembers8115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8115
def independentCachedBranchMembers8117 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8117 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8117 40 5
  · have he : independentCachedBranchMembers8117.erase 40=independentCachedBranchMembers8107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8107
  · have he : independentCachedBranchMembers8117.filter (independentCachedEdge 40)=independentCachedBranchMembers8116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8116
def independentCachedBranchMembers8118 : Finset ℕ := ([1590,1614,1644,1650,1690,1702,1720,1762,2620,2650,2662,2680,2702,2738,2762,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8118 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8118 5 (fun x => (if x<2702 then (if x<1720 then (if x<1650 then (if x<1614 then 0 else (if x<1644 then 0 else 1)) else (if x<1690 then 1 else (if x<1702 then 0 else 1))) else (if x<2650 then (if x<1762 then 1 else (if x<2620 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 0 else 1)))) else (if x<3164 then (if x<2772 then (if x<2738 then 2 else (if x<2762 then 0 else 0)) else (if x<2792 then 2 else (if x<3130 then 2 else 3))) else (if x<3252 then (if x<3222 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8119 : Finset ℕ := ([1590,1614,1644,1702,2620,2662,2702,2772,3164,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8119 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8119 4 (fun x => (if x<2702 then (if x<1702 then (if x<1614 then 0 else (if x<1644 then 0 else 1)) else (if x<2620 then 1 else (if x<2662 then 2 else 0))) else (if x<3222 then (if x<2772 then 2 else (if x<3164 then 2 else 1)) else (if x<3252 then 1 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8120 : Finset ℕ := ([250,1590,1614,1644,1650,1690,1702,1720,1762,2620,2650,2662,2680,2702,2738,2762,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8120 250 4
  · have he : independentCachedBranchMembers8120.erase 250=independentCachedBranchMembers8118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8118
  · have he : independentCachedBranchMembers8120.filter (independentCachedEdge 250)=independentCachedBranchMembers8119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8119
def independentCachedBranchMembers8121 : Finset ℕ := ([1590,1614,1650,1720,2650,2662,2772,2792,3130,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8121 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8121 4 (fun x => (if x<2772 then (if x<1720 then (if x<1614 then 0 else (if x<1650 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 2 else 0))) else (if x<3252 then (if x<2792 then 2 else (if x<3130 then 2 else 1)) else (if x<3276 then 3 else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8122 : Finset ℕ := ([130,250,1590,1614,1644,1650,1690,1702,1720,1762,2620,2650,2662,2680,2702,2738,2762,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8122 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8122 130 4
  · have he : independentCachedBranchMembers8122.erase 130=independentCachedBranchMembers8120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8120
  · have he : independentCachedBranchMembers8122.filter (independentCachedEdge 130)=independentCachedBranchMembers8121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8121
def independentCachedBranchMembers8123 : Finset ℕ := ([1650,1690,1720,1762,2620,2662,2702,2772,3130,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8123 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8123 4 (fun x => (if x<2702 then (if x<1762 then (if x<1690 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2662 then 1 else 0))) else (if x<3242 then (if x<2772 then 0 else (if x<3130 then 2 else 2)) else (if x<3282 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8124 : Finset ℕ := ([72,130,250,1590,1614,1644,1650,1690,1702,1720,1762,2620,2650,2662,2680,2702,2738,2762,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8124 72 4
  · have he : independentCachedBranchMembers8124.erase 72=independentCachedBranchMembers8122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8122
  · have he : independentCachedBranchMembers8124.filter (independentCachedEdge 72)=independentCachedBranchMembers8123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8123
def independentCachedBranchMembers8125 : Finset ℕ := ([1644,1690,1702,1762,2650,2662,2772,2792,3164,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8125 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8125 4 (fun x => (if x<2772 then (if x<1762 then (if x<1690 then 0 else (if x<1702 then 1 else 0)) else (if x<2650 then 1 else (if x<2662 then 2 else 0))) else (if x<3222 then (if x<2792 then 2 else (if x<3164 then 2 else 3)) else (if x<3242 then 3 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8126 : Finset ℕ := ([48,72,130,250,1590,1614,1644,1650,1690,1702,1720,1762,2620,2650,2662,2680,2702,2738,2762,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8126 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8126 48 4
  · have he : independentCachedBranchMembers8126.erase 48=independentCachedBranchMembers8124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8124
  · have he : independentCachedBranchMembers8126.filter (independentCachedEdge 48)=independentCachedBranchMembers8125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8125
def independentCachedBranchMembers8127 : Finset ℕ := ([48,72,130,250,1590,1614,1690,1762,2620,2650,2702,2792,3130,3164,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8127 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8127 4 (fun x => (if x<2620 then (if x<1590 then (if x<130 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1614 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3130 then (if x<2702 then (if x<2650 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3222 then (if x<3164 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
