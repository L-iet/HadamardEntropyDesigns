/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch163
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8032 : Finset ℕ := ([1582,1614,1650,1652,1720,1752,1762,1764,2680,2738,2772,3130,3132,3162,3164,3174,3222,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8032 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8032 5 (fun x => (if x<2772 then (if x<1752 then (if x<1650 then (if x<1614 then 0 else 1) else (if x<1652 then 0 else (if x<1720 then 1 else 0))) else (if x<1764 then (if x<1762 then 1 else 1) else (if x<2680 then 0 else (if x<2738 then 2 else 2)))) else (if x<3174 then (if x<3132 then (if x<3130 then 2 else 0) else (if x<3162 then 3 else (if x<3164 then 3 else 1))) else (if x<3242 then (if x<3222 then 0 else 2) else (if x<3276 then 3 else (if x<3312 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8033 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2662,2680,2710,2732,2738,2762,2772,2800,3130,3132,3162,3164,3174,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8033 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8033 2710 5
  · have he : independentCachedBranchMembers8033.erase 2710=independentCachedBranchMembers8031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8031
  · have he : independentCachedBranchMembers8033.filter (independentCachedEdge 2710)=independentCachedBranchMembers8032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8032
def independentCachedBranchMembers8034 : Finset ℕ := ([1582,1590,1644,1652,1692,1720,1734,1762,2680,2732,2762,3132,3162,3174,3214,3222,3242,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8034 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8034 5 (fun x => (if x<2762 then (if x<1720 then (if x<1644 then (if x<1590 then 0 else 1) else (if x<1652 then 1 else (if x<1692 then 0 else 0))) else (if x<1762 then (if x<1734 then 1 else 0) else (if x<2680 then 1 else (if x<2732 then 2 else 2)))) else (if x<3222 then (if x<3162 then (if x<3132 then 2 else 0) else (if x<3174 then 2 else (if x<3214 then 0 else 0))) else (if x<3276 then (if x<3242 then 3 else 3) else (if x<3304 then 3 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8035 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2650,2662,2680,2710,2732,2738,2762,2772,2800,3130,3132,3162,3164,3174,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8035 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8035 2650 5
  · have he : independentCachedBranchMembers8035.erase 2650=independentCachedBranchMembers8033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8033
  · have he : independentCachedBranchMembers8035.filter (independentCachedEdge 2650)=independentCachedBranchMembers8034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8034
def independentCachedBranchMembers8036 : Finset ℕ := ([1614,1622,1642,1650,1690,1702,1752,1764,2680,2732,2762,3132,3162,3174,3214,3222,3242,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8036 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8036 5 (fun x => (if x<2762 then (if x<1702 then (if x<1642 then (if x<1622 then 0 else 1) else (if x<1650 then 1 else (if x<1690 then 0 else 0))) else (if x<1764 then (if x<1752 then 0 else 1) else (if x<2680 then 1 else (if x<2732 then 2 else 2)))) else (if x<3222 then (if x<3162 then (if x<3132 then 2 else 2) else (if x<3174 then 0 else (if x<3214 then 0 else 0))) else (if x<3276 then (if x<3242 then 3 else 3) else (if x<3304 then 3 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8037 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2620,2650,2662,2680,2710,2732,2738,2762,2772,2800,3130,3132,3162,3164,3174,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8037 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8037 2620 5
  · have he : independentCachedBranchMembers8037.erase 2620=independentCachedBranchMembers8035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8035
  · have he : independentCachedBranchMembers8037.filter (independentCachedEdge 2620)=independentCachedBranchMembers8036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8036
def independentCachedBranchMembers8038 : Finset ℕ := ([1582,1590,1614,1622,1690,1692,1762,1764,2662,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8038 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8038 5 (fun x => (if x<2738 then (if x<1692 then (if x<1614 then (if x<1590 then 0 else 1) else (if x<1622 then 1 else (if x<1690 then 0 else 0))) else (if x<2662 then (if x<1762 then 1 else (if x<1764 then 0 else 1)) else (if x<2680 then 0 else (if x<2732 then 2 else 2)))) else (if x<3162 then (if x<2772 then (if x<2762 then 2 else 2) else (if x<3130 then 2 else (if x<3132 then 3 else 4))) else (if x<3222 then (if x<3164 then 4 else (if x<3214 then 3 else 3)) else (if x<3304 then 4 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8039 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2620,2650,2662,2680,2710,2732,2738,2762,2772,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8039 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8039 3192 5
  · have he : independentCachedBranchMembers8039.erase 3192=independentCachedBranchMembers8037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8037
  · have he : independentCachedBranchMembers8039.filter (independentCachedEdge 3192)=independentCachedBranchMembers8038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8038
def independentCachedBranchMembers8040 : Finset ℕ := ([1582,1614,1650,1652,1690,1692,1702,1734,2680,2710,2732,2762,2800,3130,3132,3162,3164,3174,3214,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8040 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8040 5 (fun x => (if x<2762 then (if x<1692 then (if x<1650 then (if x<1614 then 0 else 1) else (if x<1652 then 0 else (if x<1690 then 1 else 0))) else (if x<2680 then (if x<1702 then 1 else (if x<1734 then 1 else 0)) else (if x<2710 then 2 else (if x<2732 then 3 else 2)))) else (if x<3164 then (if x<3130 then (if x<2800 then 2 else 3) else (if x<3132 then 0 else (if x<3162 then 2 else 2))) else (if x<3252 then (if x<3174 then 1 else (if x<3214 then 0 else 0)) else (if x<3282 then 1 else (if x<3304 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8041 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2620,2650,2662,2680,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8041 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8041 2792 5
  · have he : independentCachedBranchMembers8041.erase 2792=independentCachedBranchMembers8039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8039
  · have he : independentCachedBranchMembers8041.filter (independentCachedEdge 2792)=independentCachedBranchMembers8040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8040
def independentCachedBranchMembers8042 : Finset ℕ := ([1590,1622,1642,1644,1720,1752,1762,1764,2680,2710,2732,2762,2800,3130,3132,3162,3164,3174,3214,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8042 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8042 5 (fun x => (if x<2762 then (if x<1752 then (if x<1642 then (if x<1622 then 0 else 1) else (if x<1644 then 0 else (if x<1720 then 1 else 0))) else (if x<2680 then (if x<1762 then 1 else (if x<1764 then 1 else 0)) else (if x<2710 then 2 else (if x<2732 then 3 else 2)))) else (if x<3164 then (if x<3130 then (if x<2800 then 2 else 3) else (if x<3132 then 0 else (if x<3162 then 2 else 2))) else (if x<3252 then (if x<3174 then 1 else (if x<3214 then 0 else 2)) else (if x<3282 then 0 else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8043 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2620,2650,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8043 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8043 2702 5
  · have he : independentCachedBranchMembers8043.erase 2702=independentCachedBranchMembers8041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8041
  · have he : independentCachedBranchMembers8043.filter (independentCachedEdge 2702)=independentCachedBranchMembers8042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8042
def independentCachedBranchMembers8044 : Finset ℕ := ([1582,1590,1642,1650,1690,1720,1734,1764,2620,2650,2680,2738,2772,3130,3164,3174,3214,3222,3252,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8044 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8044 5 (fun x => (if x<2738 then (if x<1720 then (if x<1642 then (if x<1590 then 0 else 1) else (if x<1650 then 1 else (if x<1690 then 0 else 0))) else (if x<2620 then (if x<1734 then 1 else (if x<1764 then 0 else 1)) else (if x<2650 then 2 else (if x<2680 then 2 else 3)))) else (if x<3214 then (if x<3130 then (if x<2772 then 2 else 2) else (if x<3164 then 0 else (if x<3174 then 2 else 0))) else (if x<3282 then (if x<3222 then 0 else (if x<3252 then 3 else 1)) else (if x<3304 then 0 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8045 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8045 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8045 2652 5
  · have he : independentCachedBranchMembers8045.erase 2652=independentCachedBranchMembers8043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8043
  · have he : independentCachedBranchMembers8045.filter (independentCachedEdge 2652)=independentCachedBranchMembers8044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8044
def independentCachedBranchMembers8046 : Finset ℕ := ([1614,1622,1644,1652,1692,1702,1752,1762,2620,2650,2680,2738,2772,3130,3164,3174,3214,3222,3252,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8046 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8046 5 (fun x => (if x<2738 then (if x<1702 then (if x<1644 then (if x<1622 then 0 else 1) else (if x<1652 then 1 else (if x<1692 then 0 else 0))) else (if x<2620 then (if x<1752 then 0 else (if x<1762 then 1 else 1)) else (if x<2650 then 2 else (if x<2680 then 2 else 3)))) else (if x<3214 then (if x<3130 then (if x<2772 then 2 else 2) else (if x<3164 then 2 else (if x<3174 then 0 else 0))) else (if x<3282 then (if x<3222 then 0 else (if x<3252 then 3 else 0)) else (if x<3304 then 1 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8047 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8047 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8047 2618 5
  · have he : independentCachedBranchMembers8047.erase 2618=independentCachedBranchMembers8045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8045
  · have he : independentCachedBranchMembers8047.filter (independentCachedEdge 2618)=independentCachedBranchMembers8046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8046
def independentCachedBranchMembers8048 : Finset ℕ := ([1590,1614,1622,1642,1650,1690,1702,1734,2618,2650,2662,2702,2710,2738,2762,3130,3162,3174,3214,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8048 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8048 5 (fun x => (if x<2702 then (if x<1690 then (if x<1622 then (if x<1614 then 0 else 0) else (if x<1642 then 1 else (if x<1650 then 1 else 2))) else (if x<2618 then (if x<1702 then 0 else (if x<1734 then 1 else 2)) else (if x<2650 then 2 else (if x<2662 then 1 else 0)))) else (if x<3162 then (if x<2738 then (if x<2710 then 2 else 1) else (if x<2762 then 0 else (if x<3130 then 0 else 3))) else (if x<3222 then (if x<3174 then 4 else (if x<3214 then 3 else 3)) else (if x<3242 then 4 else (if x<3282 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8049 : Finset ℕ := ([1590,1614,1642,1702,2650,2710,2738,2762,3162,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8049 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8049 4 (fun x => (if x<2710 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1702 then 1 else (if x<2650 then 1 else 1))) else (if x<2762 then (if x<2738 then 1 else 0) else (if x<3162 then 0 else (if x<3222 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8050 : Finset ℕ := ([1582,1590,1614,1622,1642,1650,1690,1702,1734,2618,2650,2662,2702,2710,2738,2762,3130,3162,3174,3214,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8050 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8050 1582 4
  · have he : independentCachedBranchMembers8050.erase 1582=independentCachedBranchMembers8048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8048
  · have he : independentCachedBranchMembers8050.filter (independentCachedEdge 1582)=independentCachedBranchMembers8049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8049
def independentCachedBranchMembers8051 : Finset ℕ := ([1642,1650,1702,1734,2618,2650,2702,2710,3130,3162,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8051 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8051 4 (fun x => (if x<2702 then (if x<1734 then (if x<1650 then 0 else (if x<1702 then 1 else 0)) else (if x<2618 then 1 else (if x<2650 then 1 else 0))) else (if x<3162 then (if x<2710 then 1 else (if x<3130 then 0 else 2)) else (if x<3214 then 3 else (if x<3222 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8052 : Finset ℕ := ([1582,1590,1614,1622,1642,1650,1690,1702,1734,1762,2618,2650,2662,2702,2710,2738,2762,3130,3162,3174,3214,3222,3242,3282] : List ℕ).toFinset
theorem independentCachedBranchBound8052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8052 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8052 1762 4
  · have he : independentCachedBranchMembers8052.erase 1762=independentCachedBranchMembers8050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8050
  · have he : independentCachedBranchMembers8052.filter (independentCachedEdge 1762)=independentCachedBranchMembers8051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8051
def independentCachedBranchMembers8053 : Finset ℕ := ([252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8053 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8053 252 5
  · have he : independentCachedBranchMembers8053.erase 252=independentCachedBranchMembers8047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8047
  · have he : independentCachedBranchMembers8053.filter (independentCachedEdge 252)=independentCachedBranchMembers8052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8052
def independentCachedBranchMembers8054 : Finset ℕ := ([1590,1614,1622,1644,1652,1720,1752,1762,2620,2652,2662,2738,2762,2792,2800,3132,3164,3174,3242,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8054 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8054 5 (fun x => (if x<2738 then (if x<1720 then (if x<1622 then (if x<1614 then 0 else 0) else (if x<1644 then 1 else (if x<1652 then 1 else 2))) else (if x<2620 then (if x<1752 then 2 else (if x<1762 then 1 else 0)) else (if x<2652 then 2 else (if x<2662 then 1 else 0)))) else (if x<3164 then (if x<2792 then (if x<2762 then 0 else 0) else (if x<2800 then 1 else (if x<3132 then 2 else 3))) else (if x<3282 then (if x<3174 then 4 else (if x<3242 then 3 else 3)) else (if x<3304 then 4 else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8055 : Finset ℕ := ([1590,1614,1644,1752,2652,2738,2762,2792,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8055 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8055 4 (fun x => (if x<2738 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1752 then 1 else (if x<2652 then 1 else 1))) else (if x<2792 then (if x<2762 then 0 else 0) else (if x<3164 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8056 : Finset ℕ := ([1582,1590,1614,1622,1644,1652,1720,1752,1762,2620,2652,2662,2738,2762,2792,2800,3132,3164,3174,3242,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8056 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8056 1582 4
  · have he : independentCachedBranchMembers8056.erase 1582=independentCachedBranchMembers8054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8054
  · have he : independentCachedBranchMembers8056.filter (independentCachedEdge 1582)=independentCachedBranchMembers8055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8055
def independentCachedBranchMembers8057 : Finset ℕ := ([1644,1652,1720,1752,2620,2652,2792,2800,3132,3164,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8057 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8057 4 (fun x => (if x<2792 then (if x<1752 then (if x<1652 then 0 else (if x<1720 then 1 else 0)) else (if x<2620 then 1 else (if x<2652 then 0 else 1))) else (if x<3164 then (if x<2800 then 0 else (if x<3132 then 1 else 2)) else (if x<3304 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8058 : Finset ℕ := ([1582,1590,1614,1622,1644,1652,1690,1720,1752,1762,2620,2652,2662,2738,2762,2792,2800,3132,3164,3174,3242,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8058 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8058 1690 4
  · have he : independentCachedBranchMembers8058.erase 1690=independentCachedBranchMembers8056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8056
  · have he : independentCachedBranchMembers8058.filter (independentCachedEdge 1690)=independentCachedBranchMembers8057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8057
def independentCachedBranchMembers8059 : Finset ℕ := ([132,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8059 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8059 132 5
  · have he : independentCachedBranchMembers8059.erase 132=independentCachedBranchMembers8053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8053
  · have he : independentCachedBranchMembers8059.filter (independentCachedEdge 132)=independentCachedBranchMembers8058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8058
def independentCachedBranchMembers8060 : Finset ℕ := ([1582,1622,1650,1652,1690,1692,1720,1734,1762,1764,2618,2620,2662,2702,2732,2772,2800,3130,3132,3174,3214,3242,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8060 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8060 5 (fun x => (if x<2662 then (if x<1720 then (if x<1652 then (if x<1622 then 0 else (if x<1650 then 0 else 1)) else (if x<1690 then 2 else (if x<1692 then 0 else 2))) else (if x<1764 then (if x<1734 then 1 else (if x<1762 then 2 else 0)) else (if x<2618 then 1 else (if x<2620 then 1 else 2)))) else (if x<3132 then (if x<2772 then (if x<2702 then 0 else (if x<2732 then 2 else 1)) else (if x<2800 then 2 else (if x<3130 then 1 else 3))) else (if x<3242 then (if x<3174 then 4 else (if x<3214 then 3 else 3)) else (if x<3282 then 4 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8061 : Finset ℕ := ([72,132,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8061 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8061 72 5
  · have he : independentCachedBranchMembers8061.erase 72=independentCachedBranchMembers8059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8059
  · have he : independentCachedBranchMembers8061.filter (independentCachedEdge 72)=independentCachedBranchMembers8060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8060
def independentCachedBranchMembers8062 : Finset ℕ := ([1622,1642,1644,1692,1702,1752,1764,2650,2652,2662,2710,2732,2772,2792,3162,3164,3174,3222,3242,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8062 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8062 5 (fun x => (if x<2710 then (if x<1752 then (if x<1644 then (if x<1642 then 0 else 0) else (if x<1692 then 1 else (if x<1702 then 1 else 0))) else (if x<2650 then (if x<1764 then 2 else 2) else (if x<2652 then 0 else (if x<2662 then 1 else 0)))) else (if x<3164 then (if x<2772 then (if x<2732 then 0 else 1) else (if x<2792 then 2 else (if x<3162 then 2 else 3))) else (if x<3242 then (if x<3174 then 4 else (if x<3222 then 3 else 3)) else (if x<3282 then 3 else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8063 : Finset ℕ := ([1642,1692,1702,1764,2650,2710,2732,2772,3162,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8063 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8063 4 (fun x => (if x<2710 then (if x<1702 then (if x<1692 then 0 else 1) else (if x<1764 then 0 else (if x<2650 then 1 else 0))) else (if x<2772 then (if x<2732 then 0 else 1) else (if x<3162 then 1 else (if x<3222 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
