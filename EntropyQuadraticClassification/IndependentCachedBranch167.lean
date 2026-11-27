/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch166
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8128 : Finset ℕ := ([48,72,130,250,1590,1614,1644,1650,1690,1702,1720,1762,2620,2650,2662,2680,2702,2732,2738,2762,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8128 2732 4
  · have he : independentCachedBranchMembers8128.erase 2732=independentCachedBranchMembers8126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8126
  · have he : independentCachedBranchMembers8128.filter (independentCachedEdge 2732)=independentCachedBranchMembers8127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8127
def independentCachedBranchMembers8129 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8129 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8129 3284 5
  · have he : independentCachedBranchMembers8129.erase 3284=independentCachedBranchMembers8117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8117
  · have he : independentCachedBranchMembers8129.filter (independentCachedEdge 3284)=independentCachedBranchMembers8128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8128
def independentCachedBranchMembers8130 : Finset ℕ := ([1582,1622,1644,1650,1692,1702,1720,1764,2618,2652,2662,2680,2710,2732,2762,2772,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8130 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8130 5 (fun x => (if x<2710 then (if x<1720 then (if x<1650 then (if x<1622 then 0 else (if x<1644 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 0 else 1))) else (if x<2652 then (if x<1764 then 1 else (if x<2618 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 0 else 1)))) else (if x<3162 then (if x<2772 then (if x<2732 then 2 else (if x<2762 then 0 else 2)) else (if x<2800 then 0 else (if x<3132 then 2 else 3))) else (if x<3252 then (if x<3214 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8131 : Finset ℕ := ([1582,1622,1650,1702,2618,2662,2710,2762,3162,3214,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8131 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8131 4 (fun x => (if x<2710 then (if x<1702 then (if x<1622 then 0 else (if x<1650 then 0 else 1)) else (if x<2618 then 1 else (if x<2662 then 2 else 0))) else (if x<3214 then (if x<2762 then 2 else (if x<3162 then 2 else 1)) else (if x<3242 then 1 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8132 : Finset ℕ := ([252,1582,1622,1644,1650,1692,1702,1720,1764,2618,2652,2662,2680,2710,2732,2762,2772,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8132 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8132 252 4
  · have he : independentCachedBranchMembers8132.erase 252=independentCachedBranchMembers8130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8130
  · have he : independentCachedBranchMembers8132.filter (independentCachedEdge 252)=independentCachedBranchMembers8131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8131
def independentCachedBranchMembers8133 : Finset ℕ := ([1582,1622,1644,1720,2652,2662,2762,2800,3132,3242,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8133 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8133 4 (fun x => (if x<2762 then (if x<1720 then (if x<1622 then 0 else (if x<1644 then 0 else 1)) else (if x<2652 then 1 else (if x<2662 then 2 else 0))) else (if x<3242 then (if x<2800 then 2 else (if x<3132 then 2 else 1)) else (if x<3282 then 3 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8134 : Finset ℕ := ([132,252,1582,1622,1644,1650,1692,1702,1720,1764,2618,2652,2662,2680,2710,2732,2762,2772,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8134 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8134 132 4
  · have he : independentCachedBranchMembers8134.erase 132=independentCachedBranchMembers8132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8132
  · have he : independentCachedBranchMembers8134.filter (independentCachedEdge 132)=independentCachedBranchMembers8133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8133
def independentCachedBranchMembers8135 : Finset ℕ := ([1644,1692,1720,1764,2618,2662,2710,2762,3132,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8135 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8135 4 (fun x => (if x<2710 then (if x<1764 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2662 then 1 else 0))) else (if x<3252 then (if x<2762 then 0 else (if x<3132 then 2 else 2)) else (if x<3276 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8136 : Finset ℕ := ([80,132,252,1582,1622,1644,1650,1692,1702,1720,1764,2618,2652,2662,2680,2710,2732,2762,2772,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8136 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8136 80 4
  · have he : independentCachedBranchMembers8136.erase 80=independentCachedBranchMembers8134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8134
  · have he : independentCachedBranchMembers8136.filter (independentCachedEdge 80)=independentCachedBranchMembers8135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8135
def independentCachedBranchMembers8137 : Finset ℕ := ([1650,1692,1702,1764,2652,2662,2762,2800,3162,3214,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8137 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8137 4 (fun x => (if x<2762 then (if x<1764 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<2652 then 1 else (if x<2662 then 2 else 0))) else (if x<3214 then (if x<2800 then 2 else (if x<3162 then 2 else 3)) else (if x<3252 then 3 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8138 : Finset ℕ := ([40,80,132,252,1582,1622,1644,1650,1692,1702,1720,1764,2618,2652,2662,2680,2710,2732,2762,2772,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8138 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8138 40 4
  · have he : independentCachedBranchMembers8138.erase 40=independentCachedBranchMembers8136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8136
  · have he : independentCachedBranchMembers8138.filter (independentCachedEdge 40)=independentCachedBranchMembers8137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8137
def independentCachedBranchMembers8139 : Finset ℕ := ([40,80,132,252,1582,1622,1692,1764,2618,2652,2710,2800,3132,3162,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8139 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8139 4 (fun x => (if x<2618 then (if x<1582 then (if x<132 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1622 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3132 then (if x<2710 then (if x<2652 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3214 then (if x<3162 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8140 : Finset ℕ := ([40,80,132,252,1582,1622,1644,1650,1692,1702,1720,1764,2618,2652,2662,2680,2710,2732,2738,2762,2772,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8140 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8140 2738 4
  · have he : independentCachedBranchMembers8140.erase 2738=independentCachedBranchMembers8138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8138
  · have he : independentCachedBranchMembers8140.filter (independentCachedEdge 2738)=independentCachedBranchMembers8139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8139
def independentCachedBranchMembers8141 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8141 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8141 3274 5
  · have he : independentCachedBranchMembers8141.erase 3274=independentCachedBranchMembers8129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8129
  · have he : independentCachedBranchMembers8141.filter (independentCachedEdge 3274)=independentCachedBranchMembers8140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8140
def independentCachedBranchMembers8142 : Finset ℕ := ([1582,1622,1642,1652,1692,1734,1752,1764,2620,2650,2662,2680,2702,2732,2738,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8142 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8142 5 (fun x => (if x<2702 then (if x<1752 then (if x<1652 then (if x<1622 then 0 else (if x<1642 then 0 else 1)) else (if x<1692 then 1 else (if x<1734 then 0 else 1))) else (if x<2650 then (if x<1764 then 1 else (if x<2620 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 0 else 1)))) else (if x<3164 then (if x<2772 then (if x<2732 then 2 else (if x<2738 then 0 else 2)) else (if x<2792 then 0 else (if x<3130 then 2 else 3))) else (if x<3252 then (if x<3222 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8143 : Finset ℕ := ([1582,1622,1642,1734,2650,2662,2702,2738,3130,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8143 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8143 4 (fun x => (if x<2702 then (if x<1734 then (if x<1622 then 0 else (if x<1642 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 2 else 0))) else (if x<3222 then (if x<2738 then 2 else (if x<3130 then 2 else 1)) else (if x<3242 then 1 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8144 : Finset ℕ := ([252,1582,1622,1642,1652,1692,1734,1752,1764,2620,2650,2662,2680,2702,2732,2738,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8144 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8144 252 4
  · have he : independentCachedBranchMembers8144.erase 252=independentCachedBranchMembers8142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8142
  · have he : independentCachedBranchMembers8144.filter (independentCachedEdge 252)=independentCachedBranchMembers8143 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8143
def independentCachedBranchMembers8145 : Finset ℕ := ([1582,1622,1652,1752,2620,2662,2738,2792,3164,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8145 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8145 4 (fun x => (if x<2738 then (if x<1752 then (if x<1622 then 0 else (if x<1652 then 0 else 1)) else (if x<2620 then 1 else (if x<2662 then 2 else 0))) else (if x<3242 then (if x<2792 then 2 else (if x<3164 then 2 else 1)) else (if x<3282 then 3 else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8146 : Finset ℕ := ([132,252,1582,1622,1642,1652,1692,1734,1752,1764,2620,2650,2662,2680,2702,2732,2738,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8146 132 4
  · have he : independentCachedBranchMembers8146.erase 132=independentCachedBranchMembers8144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8144
  · have he : independentCachedBranchMembers8146.filter (independentCachedEdge 132)=independentCachedBranchMembers8145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8145
def independentCachedBranchMembers8147 : Finset ℕ := ([1642,1692,1734,1764,2620,2662,2738,2792,3130,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8147 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8147 4 (fun x => (if x<2738 then (if x<1764 then (if x<1692 then 0 else (if x<1734 then 1 else 0)) else (if x<2620 then 1 else (if x<2662 then 2 else 0))) else (if x<3222 then (if x<2792 then 2 else (if x<3130 then 2 else 3)) else (if x<3252 then 3 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8148 : Finset ℕ := ([80,132,252,1582,1622,1642,1652,1692,1734,1752,1764,2620,2650,2662,2680,2702,2732,2738,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8148 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8148 80 4
  · have he : independentCachedBranchMembers8148.erase 80=independentCachedBranchMembers8146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8146
  · have he : independentCachedBranchMembers8148.filter (independentCachedEdge 80)=independentCachedBranchMembers8147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8147
def independentCachedBranchMembers8149 : Finset ℕ := ([1652,1692,1752,1764,2650,2662,2702,2738,3164,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8149 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8149 4 (fun x => (if x<2702 then (if x<1764 then (if x<1692 then 0 else (if x<1752 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 1 else 0))) else (if x<3252 then (if x<2738 then 0 else (if x<3164 then 2 else 2)) else (if x<3276 then 2 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8150 : Finset ℕ := ([40,80,132,252,1582,1622,1642,1652,1692,1734,1752,1764,2620,2650,2662,2680,2702,2732,2738,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8150 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8150 40 4
  · have he : independentCachedBranchMembers8150.erase 40=independentCachedBranchMembers8148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8148
  · have he : independentCachedBranchMembers8150.filter (independentCachedEdge 40)=independentCachedBranchMembers8149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8149
def independentCachedBranchMembers8151 : Finset ℕ := ([40,80,132,252,1582,1622,1692,1764,2620,2650,2702,2792,3130,3164,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8151 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8151 4 (fun x => (if x<2620 then (if x<1582 then (if x<132 then (if x<80 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1622 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3130 then (if x<2702 then (if x<2650 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3222 then (if x<3164 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8152 : Finset ℕ := ([40,80,132,252,1582,1622,1642,1652,1692,1734,1752,1764,2620,2650,2662,2680,2702,2732,2738,2762,2772,2792,3130,3164,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8152 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8152 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8152 2762 4
  · have he : independentCachedBranchMembers8152.erase 2762=independentCachedBranchMembers8150 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8150
  · have he : independentCachedBranchMembers8152.filter (independentCachedEdge 2762)=independentCachedBranchMembers8151 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8151
def independentCachedBranchMembers8153 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8153 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8153 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8153 3250 5
  · have he : independentCachedBranchMembers8153.erase 3250=independentCachedBranchMembers8141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8141
  · have he : independentCachedBranchMembers8153.filter (independentCachedEdge 3250)=independentCachedBranchMembers8152 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8152
def independentCachedBranchMembers8154 : Finset ℕ := ([1590,1614,1642,1652,1690,1734,1752,1762,2618,2652,2662,2680,2710,2732,2738,2762,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8154 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8154 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8154 5 (fun x => (if x<2710 then (if x<1752 then (if x<1652 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<1690 then 1 else (if x<1734 then 0 else 1))) else (if x<2652 then (if x<1762 then 1 else (if x<2618 then 0 else 2)) else (if x<2662 then 2 else (if x<2680 then 0 else 1)))) else (if x<3162 then (if x<2762 then (if x<2732 then 2 else (if x<2738 then 2 else 0)) else (if x<2800 then 0 else (if x<3132 then 2 else 3))) else (if x<3252 then (if x<3214 then 3 else (if x<3242 then 3 else 4)) else (if x<3282 then (if x<3276 then 4 else 4) else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8155 : Finset ℕ := ([1590,1614,1652,1734,2652,2662,2710,2732,3132,3214,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8155 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8155 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8155 4 (fun x => (if x<2710 then (if x<1734 then (if x<1614 then 0 else (if x<1652 then 0 else 1)) else (if x<2652 then 1 else (if x<2662 then 2 else 0))) else (if x<3214 then (if x<2732 then 2 else (if x<3132 then 2 else 1)) else (if x<3252 then 1 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8156 : Finset ℕ := ([250,1590,1614,1642,1652,1690,1734,1752,1762,2618,2652,2662,2680,2710,2732,2738,2762,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8156 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8156 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8156 250 4
  · have he : independentCachedBranchMembers8156.erase 250=independentCachedBranchMembers8154 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8154
  · have he : independentCachedBranchMembers8156.filter (independentCachedEdge 250)=independentCachedBranchMembers8155 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8155
def independentCachedBranchMembers8157 : Finset ℕ := ([1590,1614,1642,1752,2618,2662,2732,2800,3162,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8157 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8157 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8157 4 (fun x => (if x<2732 then (if x<1752 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<2618 then 1 else (if x<2662 then 2 else 0))) else (if x<3252 then (if x<2800 then 2 else (if x<3162 then 2 else 1)) else (if x<3276 then 3 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8158 : Finset ℕ := ([130,250,1590,1614,1642,1652,1690,1734,1752,1762,2618,2652,2662,2680,2710,2732,2738,2762,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8158 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8158 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8158 130 4
  · have he : independentCachedBranchMembers8158.erase 130=independentCachedBranchMembers8156 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8156
  · have he : independentCachedBranchMembers8158.filter (independentCachedEdge 130)=independentCachedBranchMembers8157 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8157
def independentCachedBranchMembers8159 : Finset ℕ := ([1652,1690,1734,1762,2618,2662,2732,2800,3132,3214,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8159 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8159 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8159 4 (fun x => (if x<2732 then (if x<1762 then (if x<1690 then 0 else (if x<1734 then 1 else 0)) else (if x<2618 then 1 else (if x<2662 then 2 else 0))) else (if x<3214 then (if x<2800 then 2 else (if x<3132 then 2 else 3)) else (if x<3242 then 3 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
