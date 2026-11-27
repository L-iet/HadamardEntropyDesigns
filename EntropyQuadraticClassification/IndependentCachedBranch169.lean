/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch168
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8192 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2702,2710,2732,2738,2762,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8192 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8192 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8192 1690 4
  · have he : independentCachedBranchMembers8192.erase 1690=independentCachedBranchMembers8190 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8190
  · have he : independentCachedBranchMembers8192.filter (independentCachedEdge 1690)=independentCachedBranchMembers8191 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8191
def independentCachedBranchMembers8193 : Finset ℕ := ([1590,1614,1650,1652,1720,1734,2618,2620,2702,2738,2762,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8193 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8193 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8193 4 (fun x => (if x<2618 then (if x<1652 then (if x<1614 then 0 else (if x<1650 then 0 else 1)) else (if x<1720 then 2 else (if x<1734 then 1 else 2))) else (if x<2738 then (if x<2620 then 1 else (if x<2702 then 2 else 2)) else (if x<2762 then 0 else (if x<2800 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8194 : Finset ℕ := ([1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2702,2710,2732,2738,2762,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8194 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8194 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8194 1622 4
  · have he : independentCachedBranchMembers8194.erase 1622=independentCachedBranchMembers8192 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8192
  · have he : independentCachedBranchMembers8194.filter (independentCachedEdge 1622)=independentCachedBranchMembers8193 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8193
def independentCachedBranchMembers8195 : Finset ℕ := ([1590,1614,1642,1644,1702,1752,2650,2652,2710,2738,2762,2792] : List ℕ).toFinset
theorem independentCachedBranchBound8195 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8195 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8195 4 (fun x => (if x<2650 then (if x<1644 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<1702 then 2 else (if x<1752 then 1 else 2))) else (if x<2738 then (if x<2652 then 1 else (if x<2710 then 2 else 1)) else (if x<2762 then 0 else (if x<2792 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8196 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2702,2710,2732,2738,2762,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8196 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8196 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8196 1582 4
  · have he : independentCachedBranchMembers8196.erase 1582=independentCachedBranchMembers8194 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8194
  · have he : independentCachedBranchMembers8196.filter (independentCachedEdge 1582)=independentCachedBranchMembers8195 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8195
def independentCachedBranchMembers8197 : Finset ℕ := ([1582,1590,1614,1622,1690,1692,1762,1764,2618,2620,2650,2652,2702,2710,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8197 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8197 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8197 4 (fun x => (if x<2618 then (if x<1690 then (if x<1614 then (if x<1590 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1762 then (if x<1692 then 0 else 1) else (if x<1764 then 0 else 1))) else (if x<2702 then (if x<2650 then (if x<2620 then 2 else 3) else (if x<2652 then 3 else 2)) else (if x<2792 then (if x<2710 then 2 else 3) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8198 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8198 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8198 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8198 2680 4
  · have he : independentCachedBranchMembers8198.erase 2680=independentCachedBranchMembers8196 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8196
  · have he : independentCachedBranchMembers8198.filter (independentCachedEdge 2680)=independentCachedBranchMembers8197 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8197
def independentCachedBranchMembers8199 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8199 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8199 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8199 3072 5
  · have he : independentCachedBranchMembers8199.erase 3072=independentCachedBranchMembers8185 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8185
  · have he : independentCachedBranchMembers8199.filter (independentCachedEdge 3072)=independentCachedBranchMembers8198 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8198
def independentCachedBranchMembers8200 : Finset ℕ := ([132,252,1590,1614,1642,1652,1692,1702,1720,1764,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8200 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8200 5 (fun x => (if x<2732 then (if x<1692 then (if x<1614 then (if x<252 then 0 else (if x<1590 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 2 else 2))) else (if x<1764 then (if x<1702 then 0 else (if x<1720 then 2 else 2)) else (if x<2650 then (if x<2620 then 0 else 3) else (if x<2710 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 0 else (if x<2762 then 1 else 1)) else (if x<3130 then (if x<2800 then 0 else 3) else (if x<3164 then 4 else 4))) else (if x<3252 then (if x<3192 then 2 else (if x<3214 then 2 else 4)) else (if x<3282 then (if x<3276 then 0 else 0) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8201 : Finset ℕ := ([1652,1692,1720,1764,2620,2732,2772,2800,3130,3174,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8201 4 (fun x => (if x<2772 then (if x<1764 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2732 then 0 else 1))) else (if x<3174 then (if x<2800 then 0 else (if x<3130 then 1 else 2)) else (if x<3214 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8202 : Finset ℕ := ([72,132,252,1590,1614,1642,1652,1692,1702,1720,1764,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8202 72 4
  · have he : independentCachedBranchMembers8202.erase 72=independentCachedBranchMembers8200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8200
  · have he : independentCachedBranchMembers8202.filter (independentCachedEdge 72)=independentCachedBranchMembers8201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8201
def independentCachedBranchMembers8203 : Finset ℕ := ([1642,1692,1702,1764,2650,2710,2732,2772,3164,3174,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8203 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8203 4 (fun x => (if x<2732 then (if x<1764 then (if x<1692 then 0 else (if x<1702 then 1 else 0)) else (if x<2650 then 1 else (if x<2710 then 0 else 0))) else (if x<3174 then (if x<2772 then 1 else (if x<3164 then 1 else 2)) else (if x<3282 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8204 : Finset ℕ := ([48,72,132,252,1590,1614,1642,1652,1692,1702,1720,1764,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8204 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8204 48 4
  · have he : independentCachedBranchMembers8204.erase 48=independentCachedBranchMembers8202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8202
  · have he : independentCachedBranchMembers8204.filter (independentCachedEdge 48)=independentCachedBranchMembers8203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8203
def independentCachedBranchMembers8205 : Finset ℕ := ([48,72,132,252,1590,1614,1692,1764,2620,2650,2710,2800,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8205 4 (fun x => (if x<2620 then (if x<1590 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3130 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8206 : Finset ℕ := ([48,72,132,252,1590,1614,1642,1652,1692,1702,1720,1764,2620,2650,2710,2732,2738,2762,2772,2800,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8206 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8206 3242 4
  · have he : independentCachedBranchMembers8206.erase 3242=independentCachedBranchMembers8204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8204
  · have he : independentCachedBranchMembers8206.filter (independentCachedEdge 3242)=independentCachedBranchMembers8205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8205
def independentCachedBranchMembers8207 : Finset ℕ := ([48,72,132,252,1642,1652,1702,1720,2732,2738,2762,2772,3130,3164,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8207 4 (fun x => (if x<2732 then (if x<1642 then (if x<132 then (if x<72 then 0 else 0) else (if x<252 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3130 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3214 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8208 : Finset ℕ := ([48,72,132,252,1590,1614,1642,1652,1692,1702,1720,1764,2620,2650,2710,2732,2738,2762,2772,2800,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8208 3102 4
  · have he : independentCachedBranchMembers8208.erase 3102=independentCachedBranchMembers8206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8206
  · have he : independentCachedBranchMembers8208.filter (independentCachedEdge 3102)=independentCachedBranchMembers8207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8207
def independentCachedBranchMembers8209 : Finset ℕ := ([1590,1614,1642,1652,1692,1702,1720,1764,2620,2650,2710,2732,2738,2762,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8209 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8209 4 (fun x => (if x<2620 then (if x<1692 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1764 then 1 else 0))) else (if x<2738 then (if x<2710 then (if x<2650 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2800 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8210 : Finset ℕ := ([48,72,132,252,1590,1614,1642,1652,1692,1702,1720,1764,2620,2650,2710,2732,2738,2762,2772,2800,3072,3102,3130,3164,3174,3192,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8210 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8210 3072 4
  · have he : independentCachedBranchMembers8210.erase 3072=independentCachedBranchMembers8208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8208
  · have he : independentCachedBranchMembers8210.filter (independentCachedEdge 3072)=independentCachedBranchMembers8209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8209
def independentCachedBranchMembers8211 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8211 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8211 2770 5
  · have he : independentCachedBranchMembers8211.erase 2770=independentCachedBranchMembers8199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8199
  · have he : independentCachedBranchMembers8211.filter (independentCachedEdge 2770)=independentCachedBranchMembers8210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8210
def independentCachedBranchMembers8212 : Finset ℕ := ([130,250,1582,1622,1642,1652,1690,1702,1720,1762,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8212 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8212 5 (fun x => (if x<2732 then (if x<1690 then (if x<1622 then (if x<250 then 0 else (if x<1582 then 0 else 1)) else (if x<1642 then 1 else (if x<1652 then 2 else 2))) else (if x<1762 then (if x<1702 then 0 else (if x<1720 then 2 else 2)) else (if x<2652 then (if x<2618 then 0 else 3) else (if x<2702 then 3 else 3)))) else (if x<3174 then (if x<2772 then (if x<2738 then 1 else (if x<2762 then 0 else 0)) else (if x<3132 then (if x<2792 then 1 else 3) else (if x<3162 then 4 else 4))) else (if x<3242 then (if x<3192 then 2 else (if x<3222 then 2 else 4)) else (if x<3282 then (if x<3276 then 0 else 3) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8213 : Finset ℕ := ([1642,1690,1720,1762,2618,2738,2762,2792,3132,3174,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8213 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8213 4 (fun x => (if x<2762 then (if x<1762 then (if x<1690 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2738 then 0 else 1))) else (if x<3174 then (if x<2792 then 0 else (if x<3132 then 1 else 2)) else (if x<3222 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8214 : Finset ℕ := ([80,130,250,1582,1622,1642,1652,1690,1702,1720,1762,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8214 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8214 80 4
  · have he : independentCachedBranchMembers8214.erase 80=independentCachedBranchMembers8212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8212
  · have he : independentCachedBranchMembers8214.filter (independentCachedEdge 80)=independentCachedBranchMembers8213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8213
def independentCachedBranchMembers8215 : Finset ℕ := ([1652,1690,1702,1762,2652,2702,2738,2762,3162,3174,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8215 4 (fun x => (if x<2738 then (if x<1762 then (if x<1690 then 0 else (if x<1702 then 1 else 0)) else (if x<2652 then 1 else (if x<2702 then 0 else 0))) else (if x<3174 then (if x<2762 then 1 else (if x<3162 then 1 else 2)) else (if x<3276 then 2 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8216 : Finset ℕ := ([40,80,130,250,1582,1622,1642,1652,1690,1702,1720,1762,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8216 40 4
  · have he : independentCachedBranchMembers8216.erase 40=independentCachedBranchMembers8214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8214
  · have he : independentCachedBranchMembers8216.filter (independentCachedEdge 40)=independentCachedBranchMembers8215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8215
def independentCachedBranchMembers8217 : Finset ℕ := ([40,80,130,250,1582,1622,1690,1762,2618,2652,2702,2792,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8217 4 (fun x => (if x<2618 then (if x<1582 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1622 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3132 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8218 : Finset ℕ := ([40,80,130,250,1582,1622,1642,1652,1690,1702,1720,1762,2618,2652,2702,2732,2738,2762,2772,2792,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8218 3252 4
  · have he : independentCachedBranchMembers8218.erase 3252=independentCachedBranchMembers8216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8216
  · have he : independentCachedBranchMembers8218.filter (independentCachedEdge 3252)=independentCachedBranchMembers8217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8217
def independentCachedBranchMembers8219 : Finset ℕ := ([40,80,130,250,1642,1652,1702,1720,2732,2738,2762,2772,3132,3162,3222,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8219 4 (fun x => (if x<2732 then (if x<1642 then (if x<130 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1702 then (if x<1652 then 1 else 1) else (if x<1720 then 1 else 1))) else (if x<3132 then (if x<2762 then (if x<2738 then 2 else 2) else (if x<2772 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8220 : Finset ℕ := ([40,80,130,250,1582,1622,1642,1652,1690,1702,1720,1762,2618,2652,2702,2732,2738,2762,2772,2792,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8220 3102 4
  · have he : independentCachedBranchMembers8220.erase 3102=independentCachedBranchMembers8218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8218
  · have he : independentCachedBranchMembers8220.filter (independentCachedEdge 3102)=independentCachedBranchMembers8219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8219
def independentCachedBranchMembers8221 : Finset ℕ := ([1582,1622,1642,1652,1690,1702,1720,1762,2618,2652,2702,2732,2738,2762,2772,2792] : List ℕ).toFinset
theorem independentCachedBranchBound8221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8221 4 (fun x => (if x<2618 then (if x<1690 then (if x<1642 then (if x<1622 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1720 then (if x<1702 then 0 else 1) else (if x<1762 then 1 else 0))) else (if x<2738 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2732 then 2 else 3)) else (if x<2772 then (if x<2762 then 3 else 3) else (if x<2792 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8222 : Finset ℕ := ([40,80,130,250,1582,1622,1642,1652,1690,1702,1720,1762,2618,2652,2702,2732,2738,2762,2772,2792,3072,3102,3132,3162,3174,3192,3222,3242,3252,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8222 3072 4
  · have he : independentCachedBranchMembers8222.erase 3072=independentCachedBranchMembers8220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8220
  · have he : independentCachedBranchMembers8222.filter (independentCachedEdge 3072)=independentCachedBranchMembers8221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8221
def independentCachedBranchMembers8223 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8223 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8223 2764 5
  · have he : independentCachedBranchMembers8223.erase 2764=independentCachedBranchMembers8211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8211
  · have he : independentCachedBranchMembers8223.filter (independentCachedEdge 2764)=independentCachedBranchMembers8222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8222
end EntropyDesigns.QuadraticRefinement
