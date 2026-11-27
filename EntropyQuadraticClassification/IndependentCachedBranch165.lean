/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch164
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8064 : Finset ℕ := ([1622,1642,1644,1692,1702,1752,1762,1764,2650,2652,2662,2710,2732,2772,2792,3162,3164,3174,3222,3242,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8064 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8064 1762 4
  · have he : independentCachedBranchMembers8064.erase 1762=independentCachedBranchMembers8062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8062
  · have he : independentCachedBranchMembers8064.filter (independentCachedEdge 1762)=independentCachedBranchMembers8063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8063
def independentCachedBranchMembers8065 : Finset ℕ := ([1644,1692,1752,1764,2652,2732,2772,2792,3164,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8065 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8065 4 (fun x => (if x<2732 then (if x<1752 then (if x<1692 then 0 else 0) else (if x<1764 then 1 else (if x<2652 then 1 else 0))) else (if x<2792 then (if x<2772 then 0 else 1) else (if x<3164 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8066 : Finset ℕ := ([1622,1642,1644,1690,1692,1702,1752,1762,1764,2650,2652,2662,2710,2732,2772,2792,3162,3164,3174,3222,3242,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8066 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8066 1690 4
  · have he : independentCachedBranchMembers8066.erase 1690=independentCachedBranchMembers8064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8064
  · have he : independentCachedBranchMembers8066.filter (independentCachedEdge 1690)=independentCachedBranchMembers8065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8065
def independentCachedBranchMembers8067 : Finset ℕ := ([1642,1644,1702,1752,2650,2652,2710,2792,3162,3164,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8067 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8067 4 (fun x => (if x<2710 then (if x<1752 then (if x<1644 then 0 else (if x<1702 then 1 else 0)) else (if x<2650 then 1 else (if x<2652 then 0 else 1))) else (if x<3164 then (if x<2792 then 0 else (if x<3162 then 1 else 2)) else (if x<3222 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8068 : Finset ℕ := ([1582,1622,1642,1644,1690,1692,1702,1752,1762,1764,2650,2652,2662,2710,2732,2772,2792,3162,3164,3174,3222,3242,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8068 1582 4
  · have he : independentCachedBranchMembers8068.erase 1582=independentCachedBranchMembers8066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8066
  · have he : independentCachedBranchMembers8068.filter (independentCachedEdge 1582)=independentCachedBranchMembers8067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8067
def independentCachedBranchMembers8069 : Finset ℕ := ([48,72,132,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8069 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8069 48 5
  · have he : independentCachedBranchMembers8069.erase 48=independentCachedBranchMembers8061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8061
  · have he : independentCachedBranchMembers8069.filter (independentCachedEdge 48)=independentCachedBranchMembers8068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8068
def independentCachedBranchMembers8070 : Finset ℕ := ([1590,1614,1644,1652,1692,1702,1734,2652,2662,2710,2732,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8070 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8070 5 (fun x => (if x<2710 then (if x<1692 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1652 then 1 else 2)) else (if x<1734 then (if x<1702 then 0 else 1) else (if x<2652 then 2 else (if x<2662 then 1 else 0)))) else (if x<3174 then (if x<3132 then (if x<2732 then 1 else 1) else (if x<3164 then 2 else 3)) else (if x<3222 then (if x<3214 then 2 else 2) else (if x<3252 then 3 else (if x<3276 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8071 : Finset ℕ := ([1590,1614,1644,1702,2652,2710,3132,3174,3214] : List ℕ).toFinset
theorem independentCachedBranchBound8071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8071 4 (fun x => (if x<2652 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1702 then 1 else 1)) else (if x<3132 then (if x<2710 then 1 else 1) else (if x<3174 then 2 else (if x<3214 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8072 : Finset ℕ := ([1590,1614,1644,1652,1692,1702,1734,2652,2662,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8072 2772 4
  · have he : independentCachedBranchMembers8072.erase 2772=independentCachedBranchMembers8070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8070
  · have he : independentCachedBranchMembers8072.filter (independentCachedEdge 2772)=independentCachedBranchMembers8071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8071
def independentCachedBranchMembers8073 : Finset ℕ := ([1590,1644,2710,2732,3132,3164,3174,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8073 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8073 4 (fun x => (if x<3132 then (if x<2710 then (if x<1644 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<3174 then (if x<3164 then 1 else 2) else (if x<3214 then 2 else (if x<3252 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8074 : Finset ℕ := ([1590,1614,1644,1652,1692,1702,1734,2652,2662,2702,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8074 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8074 2702 4
  · have he : independentCachedBranchMembers8074.erase 2702=independentCachedBranchMembers8072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8072
  · have he : independentCachedBranchMembers8074.filter (independentCachedEdge 2702)=independentCachedBranchMembers8073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8073
def independentCachedBranchMembers8075 : Finset ℕ := ([1614,1702,2652,2732,3132,3174,3214,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8075 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8075 4 (fun x => (if x<3132 then (if x<2652 then (if x<1702 then 0 else 0) else (if x<2732 then 0 else 1)) else (if x<3214 then (if x<3174 then 1 else 2) else (if x<3222 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8076 : Finset ℕ := ([1590,1614,1644,1652,1692,1702,1734,2620,2652,2662,2702,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8076 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8076 2620 4
  · have he : independentCachedBranchMembers8076.erase 2620=independentCachedBranchMembers8074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8074
  · have he : independentCachedBranchMembers8076.filter (independentCachedEdge 2620)=independentCachedBranchMembers8075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8075
def independentCachedBranchMembers8077 : Finset ℕ := ([1590,1614,1652,1734,2620,2702,3132,3214,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8077 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8077 4 (fun x => (if x<2702 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1734 then 1 else (if x<2620 then 1 else 1))) else (if x<3214 then (if x<3132 then 1 else 2) else (if x<3252 then 2 else (if x<3276 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8078 : Finset ℕ := ([1590,1614,1622,1644,1652,1692,1702,1734,2620,2652,2662,2702,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8078 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8078 1622 4
  · have he : independentCachedBranchMembers8078.erase 1622=independentCachedBranchMembers8076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8076
  · have he : independentCachedBranchMembers8078.filter (independentCachedEdge 1622)=independentCachedBranchMembers8077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8077
def independentCachedBranchMembers8079 : Finset ℕ := ([1590,1614,1644,1702,2652,2710,3164,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8079 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8079 4 (fun x => (if x<2710 then (if x<1644 then (if x<1614 then 0 else 0) else (if x<1702 then 1 else (if x<2652 then 1 else 1))) else (if x<3222 then (if x<3164 then 1 else 2) else (if x<3252 then 2 else (if x<3276 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8080 : Finset ℕ := ([1582,1590,1614,1622,1644,1652,1692,1702,1734,2620,2652,2662,2702,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8080 1582 4
  · have he : independentCachedBranchMembers8080.erase 1582=independentCachedBranchMembers8078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8078
  · have he : independentCachedBranchMembers8080.filter (independentCachedEdge 1582)=independentCachedBranchMembers8079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8079
def independentCachedBranchMembers8081 : Finset ℕ := ([1644,1652,1702,1734,2620,2652,2702,2710,3132,3164,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8081 4 (fun x => (if x<2702 then (if x<1734 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<2620 then 1 else (if x<2652 then 1 else 0))) else (if x<3164 then (if x<2710 then 1 else (if x<3132 then 0 else 2)) else (if x<3214 then 3 else (if x<3222 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8082 : Finset ℕ := ([1582,1590,1614,1622,1644,1652,1692,1702,1734,1764,2620,2652,2662,2702,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8082 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8082 1764 4
  · have he : independentCachedBranchMembers8082.erase 1764=independentCachedBranchMembers8080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8080
  · have he : independentCachedBranchMembers8082.filter (independentCachedEdge 1764)=independentCachedBranchMembers8081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8081
def independentCachedBranchMembers8083 : Finset ℕ := ([1582,1590,1614,1622,1702,1734,2662,2702,2710,3174,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8083 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8083 4 (fun x => (if x<2662 then (if x<1622 then (if x<1590 then 0 else (if x<1614 then 1 else 1)) else (if x<1702 then 0 else (if x<1734 then 2 else 3))) else (if x<3174 then (if x<2702 then 0 else (if x<2710 then 2 else 3)) else (if x<3214 then 1 else (if x<3222 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8084 : Finset ℕ := ([252,1582,1590,1614,1622,1644,1652,1692,1702,1734,1764,2620,2652,2662,2702,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8084 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8084 252 4
  · have he : independentCachedBranchMembers8084.erase 252=independentCachedBranchMembers8082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8082
  · have he : independentCachedBranchMembers8084.filter (independentCachedEdge 252)=independentCachedBranchMembers8083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8083
def independentCachedBranchMembers8085 : Finset ℕ := ([1582,1590,1614,1622,1644,1652,2620,2652,2662,3132,3164,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8085 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8085 4 (fun x => (if x<2620 then (if x<1622 then (if x<1590 then 0 else (if x<1614 then 1 else 1)) else (if x<1644 then 0 else (if x<1652 then 2 else 3))) else (if x<3132 then (if x<2652 then 2 else (if x<2662 then 3 else 0)) else (if x<3164 then 3 else (if x<3174 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8086 : Finset ℕ := ([132,252,1582,1590,1614,1622,1644,1652,1692,1702,1734,1764,2620,2652,2662,2702,2710,2732,2772,3132,3164,3174,3214,3222,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound8086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8086 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8086 132 4
  · have he : independentCachedBranchMembers8086.erase 132=independentCachedBranchMembers8084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8084
  · have he : independentCachedBranchMembers8086.filter (independentCachedEdge 132)=independentCachedBranchMembers8085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8085
def independentCachedBranchMembers8087 : Finset ℕ := ([48,72,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8087 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8087 250 5
  · have he : independentCachedBranchMembers8087.erase 250=independentCachedBranchMembers8069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8069
  · have he : independentCachedBranchMembers8087.filter (independentCachedEdge 250)=independentCachedBranchMembers8086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8086
def independentCachedBranchMembers8088 : Finset ℕ := ([1590,1614,1622,1642,1650,1720,1752,1764,2618,2650,2662,2732,2772,2792,2800,3130,3162,3174,3252,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8088 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8088 5 (fun x => (if x<2732 then (if x<1720 then (if x<1622 then (if x<1614 then 0 else 0) else (if x<1642 then 1 else (if x<1650 then 1 else 2))) else (if x<2618 then (if x<1752 then 2 else (if x<1764 then 1 else 0)) else (if x<2650 then 2 else (if x<2662 then 1 else 0)))) else (if x<3162 then (if x<2792 then (if x<2772 then 2 else 1) else (if x<2800 then 1 else (if x<3130 then 2 else 3))) else (if x<3276 then (if x<3174 then 4 else (if x<3252 then 3 else 3)) else (if x<3304 then 4 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8089 : Finset ℕ := ([1590,1614,1642,1752,2650,2792,3162,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8089 4 (fun x => (if x<2792 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1752 then 1 else (if x<2650 then 1 else 1))) else (if x<3252 then (if x<3162 then 1 else 2) else (if x<3276 then 0 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8090 : Finset ℕ := ([1582,1590,1614,1622,1642,1650,1720,1752,1764,2618,2650,2662,2732,2772,2792,2800,3130,3162,3174,3252,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8090 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8090 1582 4
  · have he : independentCachedBranchMembers8090.erase 1582=independentCachedBranchMembers8088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8088
  · have he : independentCachedBranchMembers8090.filter (independentCachedEdge 1582)=independentCachedBranchMembers8089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8089
def independentCachedBranchMembers8091 : Finset ℕ := ([1642,1650,1720,1752,2618,2650,2792,2800,3130,3162,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8091 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8091 4 (fun x => (if x<2792 then (if x<1752 then (if x<1650 then 0 else (if x<1720 then 1 else 0)) else (if x<2618 then 1 else (if x<2650 then 0 else 1))) else (if x<3162 then (if x<2800 then 0 else (if x<3130 then 1 else 2)) else (if x<3304 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8092 : Finset ℕ := ([1582,1590,1614,1622,1642,1650,1692,1720,1752,1764,2618,2650,2662,2732,2772,2792,2800,3130,3162,3174,3252,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8092 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8092 1692 4
  · have he : independentCachedBranchMembers8092.erase 1692=independentCachedBranchMembers8090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8090
  · have he : independentCachedBranchMembers8092.filter (independentCachedEdge 1692)=independentCachedBranchMembers8091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8091
def independentCachedBranchMembers8093 : Finset ℕ := ([1582,1590,1614,1622,1642,1650,2618,2650,2662,3130,3162,3174] : List ℕ).toFinset
theorem independentCachedBranchBound8093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8093 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8093 4 (fun x => (if x<2618 then (if x<1622 then (if x<1590 then 0 else (if x<1614 then 1 else 1)) else (if x<1642 then 0 else (if x<1650 then 2 else 3))) else (if x<3130 then (if x<2650 then 2 else (if x<2662 then 3 else 0)) else (if x<3162 then 3 else (if x<3174 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8094 : Finset ℕ := ([252,1582,1590,1614,1622,1642,1650,1692,1720,1752,1764,2618,2650,2662,2732,2772,2792,2800,3130,3162,3174,3252,3276,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8094 252 4
  · have he : independentCachedBranchMembers8094.erase 252=independentCachedBranchMembers8092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8092
  · have he : independentCachedBranchMembers8094.filter (independentCachedEdge 252)=independentCachedBranchMembers8093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8093
def independentCachedBranchMembers8095 : Finset ℕ := ([1582,1590,1614,1622,1720,1752,2662,2792,2800,3174,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8095 4 (fun x => (if x<2662 then (if x<1622 then (if x<1590 then 0 else (if x<1614 then 1 else 1)) else (if x<1720 then 0 else (if x<1752 then 2 else 3))) else (if x<3174 then (if x<2792 then 0 else (if x<2800 then 2 else 3)) else (if x<3304 then 1 else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
