/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch167
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8160 : Finset ℕ := ([72,130,250,1590,1614,1642,1652,1690,1734,1752,1762,2618,2652,2662,2680,2710,2732,2738,2762,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8160 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8160 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8160 72 4
  · have he : independentCachedBranchMembers8160.erase 72=independentCachedBranchMembers8158 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8158
  · have he : independentCachedBranchMembers8160.filter (independentCachedEdge 72)=independentCachedBranchMembers8159 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8159
def independentCachedBranchMembers8161 : Finset ℕ := ([1642,1690,1752,1762,2652,2662,2710,2732,3162,3242,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8161 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8161 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8161 4 (fun x => (if x<2710 then (if x<1762 then (if x<1690 then 0 else (if x<1752 then 0 else 1)) else (if x<2652 then 1 else (if x<2662 then 1 else 0))) else (if x<3242 then (if x<2732 then 0 else (if x<3162 then 2 else 2)) else (if x<3282 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8162 : Finset ℕ := ([48,72,130,250,1590,1614,1642,1652,1690,1734,1752,1762,2618,2652,2662,2680,2710,2732,2738,2762,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8162 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8162 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8162 48 4
  · have he : independentCachedBranchMembers8162.erase 48=independentCachedBranchMembers8160 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8160
  · have he : independentCachedBranchMembers8162.filter (independentCachedEdge 48)=independentCachedBranchMembers8161 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8161
def independentCachedBranchMembers8163 : Finset ℕ := ([48,72,130,250,1590,1614,1690,1762,2618,2652,2710,2800,3132,3162,3214,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8163 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8163 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8163 4 (fun x => (if x<2618 then (if x<1590 then (if x<130 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1690 then (if x<1614 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3132 then (if x<2710 then (if x<2652 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3214 then (if x<3162 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8164 : Finset ℕ := ([48,72,130,250,1590,1614,1642,1652,1690,1734,1752,1762,2618,2652,2662,2680,2710,2732,2738,2762,2772,2800,3132,3162,3214,3242,3252,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8164 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8164 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8164 2772 4
  · have he : independentCachedBranchMembers8164.erase 2772=independentCachedBranchMembers8162 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8162
  · have he : independentCachedBranchMembers8164.filter (independentCachedEdge 2772)=independentCachedBranchMembers8163 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8163
def independentCachedBranchMembers8165 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8165 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8165 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8165 3244 5
  · have he : independentCachedBranchMembers8165.erase 3244=independentCachedBranchMembers8153 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8153
  · have he : independentCachedBranchMembers8165.filter (independentCachedEdge 3244)=independentCachedBranchMembers8164 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8164
def independentCachedBranchMembers8166 : Finset ℕ := ([1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8166 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8166 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8166 5 (fun x => (if x<2738 then (if x<1720 then (if x<1650 then (if x<1644 then 0 else 1) else (if x<1652 then 1 else (if x<1702 then 0 else 0))) else (if x<1752 then (if x<1734 then 0 else 1) else (if x<2680 then 1 else (if x<2732 then 0 else 2)))) else (if x<3162 then (if x<2772 then (if x<2762 then 2 else 2) else (if x<3130 then 2 else (if x<3132 then 3 else 4))) else (if x<3222 then (if x<3164 then 4 else (if x<3214 then 3 else 3)) else (if x<3304 then 4 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8167 : Finset ℕ := ([1642,1650,1702,1734,2738,2762,3130,3162,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8167 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8167 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8167 4 (fun x => (if x<2762 then (if x<1702 then (if x<1650 then 0 else 1) else (if x<1734 then 0 else (if x<2738 then 1 else 2))) else (if x<3162 then (if x<3130 then 2 else 1) else (if x<3214 then 0 else (if x<3222 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8168 : Finset ℕ := ([252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8168 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8168 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8168 252 4
  · have he : independentCachedBranchMembers8168.erase 252=independentCachedBranchMembers8166 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8166
  · have he : independentCachedBranchMembers8168.filter (independentCachedEdge 252)=independentCachedBranchMembers8167 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8167
def independentCachedBranchMembers8169 : Finset ℕ := ([1644,1652,1720,1752,2738,2762,3132,3164,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8169 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8169 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8169 4 (fun x => (if x<2762 then (if x<1720 then (if x<1652 then 0 else 1) else (if x<1752 then 0 else (if x<2738 then 1 else 0))) else (if x<3164 then (if x<3132 then 1 else 2) else (if x<3304 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8170 : Finset ℕ := ([132,252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8170 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8170 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8170 132 4
  · have he : independentCachedBranchMembers8170.erase 132=independentCachedBranchMembers8168 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8168
  · have he : independentCachedBranchMembers8170.filter (independentCachedEdge 132)=independentCachedBranchMembers8169 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8169
def independentCachedBranchMembers8171 : Finset ℕ := ([1650,1652,1720,1734,2732,2772,3130,3132,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8171 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8171 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8171 4 (fun x => (if x<2772 then (if x<1720 then (if x<1652 then 0 else 1) else (if x<1734 then 0 else (if x<2732 then 1 else 0))) else (if x<3132 then (if x<3130 then 1 else 2) else (if x<3214 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8172 : Finset ℕ := ([72,132,252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8172 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8172 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8172 72 4
  · have he : independentCachedBranchMembers8172.erase 72=independentCachedBranchMembers8170 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8170
  · have he : independentCachedBranchMembers8172.filter (independentCachedEdge 72)=independentCachedBranchMembers8171 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8171
def independentCachedBranchMembers8173 : Finset ℕ := ([1642,1644,1702,1752,2732,2772,3162,3164,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8173 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8173 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8173 4 (fun x => (if x<2772 then (if x<1702 then (if x<1644 then 0 else 1) else (if x<1752 then 0 else (if x<2732 then 1 else 2))) else (if x<3164 then (if x<3162 then 2 else 0) else (if x<3222 then 1 else (if x<3304 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8174 : Finset ℕ := ([48,72,132,252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8174 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8174 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8174 48 4
  · have he : independentCachedBranchMembers8174.erase 48=independentCachedBranchMembers8172 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8172
  · have he : independentCachedBranchMembers8174.filter (independentCachedEdge 48)=independentCachedBranchMembers8173 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8173
def independentCachedBranchMembers8175 : Finset ℕ := ([132,252,1644,1652,1702,1734,2732,2772,3132,3164,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8175 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8175 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8175 4 (fun x => (if x<2732 then (if x<1652 then (if x<252 then 0 else (if x<1644 then 0 else 1)) else (if x<1702 then 2 else (if x<1734 then 1 else 2))) else (if x<3164 then (if x<2772 then 0 else (if x<3132 then 0 else 2)) else (if x<3214 then 1 else (if x<3222 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8176 : Finset ℕ := ([48,72,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8176 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8176 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8176 250 4
  · have he : independentCachedBranchMembers8176.erase 250=independentCachedBranchMembers8174 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8174
  · have he : independentCachedBranchMembers8176.filter (independentCachedEdge 250)=independentCachedBranchMembers8175 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8175
def independentCachedBranchMembers8177 : Finset ℕ := ([132,252,1642,1650,1720,1752,2732,2772,3130,3162,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8177 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8177 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8177 4 (fun x => (if x<2732 then (if x<1650 then (if x<252 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 2 else (if x<1752 then 1 else 2))) else (if x<3162 then (if x<2772 then 0 else (if x<3130 then 0 else 1)) else (if x<3304 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8178 : Finset ℕ := ([48,72,130,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8178 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8178 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8178 130 4
  · have he : independentCachedBranchMembers8178.erase 130=independentCachedBranchMembers8176 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8176
  · have he : independentCachedBranchMembers8178.filter (independentCachedEdge 130)=independentCachedBranchMembers8177 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8177
def independentCachedBranchMembers8179 : Finset ℕ := ([48,72,1642,1644,1720,1734,2738,2762,3130,3132,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8179 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8179 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8179 4 (fun x => (if x<2738 then (if x<1644 then (if x<72 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 2 else (if x<1734 then 1 else 2))) else (if x<3132 then (if x<2762 then 0 else (if x<3130 then 0 else 1)) else (if x<3222 then 2 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8180 : Finset ℕ := ([48,72,80,130,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8180 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8180 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8180 80 4
  · have he : independentCachedBranchMembers8180.erase 80=independentCachedBranchMembers8178 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8178
  · have he : independentCachedBranchMembers8180.filter (independentCachedEdge 80)=independentCachedBranchMembers8179 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8179
def independentCachedBranchMembers8181 : Finset ℕ := ([48,72,1650,1652,1702,1752,2738,2762,3162,3164,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8181 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8181 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8181 4 (fun x => (if x<2738 then (if x<1652 then (if x<72 then 0 else (if x<1650 then 0 else 1)) else (if x<1702 then 2 else (if x<1752 then 1 else 2))) else (if x<3164 then (if x<2762 then 0 else (if x<3162 then 0 else 1)) else (if x<3214 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8182 : Finset ℕ := ([40,48,72,80,130,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8182 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8182 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8182 40 4
  · have he : independentCachedBranchMembers8182.erase 40=independentCachedBranchMembers8180 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8180
  · have he : independentCachedBranchMembers8182.filter (independentCachedEdge 40)=independentCachedBranchMembers8181 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8181
def independentCachedBranchMembers8183 : Finset ℕ := ([40,48,72,80,130,132,250,252,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8183 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8183 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8183 4 (fun x => (if x<3130 then (if x<130 then (if x<72 then (if x<48 then 0 else 1) else (if x<80 then 1 else 0)) else (if x<250 then (if x<132 then 0 else 1) else (if x<252 then 0 else 1))) else (if x<3214 then (if x<3162 then (if x<3132 then 2 else 3) else (if x<3164 then 3 else 2)) else (if x<3304 then (if x<3222 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8184 : Finset ℕ := ([40,48,72,80,130,132,250,252,1642,1644,1650,1652,1702,1720,1734,1752,2662,2680,2732,2738,2762,2772,3130,3132,3162,3164,3214,3222,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8184 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8184 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8184 2662 4
  · have he : independentCachedBranchMembers8184.erase 2662=independentCachedBranchMembers8182 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8182
  · have he : independentCachedBranchMembers8184.filter (independentCachedEdge 2662)=independentCachedBranchMembers8183 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8183
def independentCachedBranchMembers8185 : Finset ℕ := ([40,48,72,80,130,132,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2772,2792,2800,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8185 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8185 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8185 3102 5
  · have he : independentCachedBranchMembers8185.erase 3102=independentCachedBranchMembers8165 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8165
  · have he : independentCachedBranchMembers8185.filter (independentCachedEdge 3102)=independentCachedBranchMembers8184 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8184
def independentCachedBranchMembers8186 : Finset ℕ := ([1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1764,2618,2620,2650,2652,2662,2702,2710,2732,2738,2762,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8186 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8186 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8186 5 (fun x => (if x<2620 then (if x<1702 then (if x<1650 then (if x<1642 then 0 else (if x<1644 then 1 else 2)) else (if x<1652 then 0 else (if x<1692 then 1 else 2))) else (if x<1752 then (if x<1720 then 0 else (if x<1734 then 1 else 2)) else (if x<1764 then 3 else (if x<2618 then 3 else 4)))) else (if x<2732 then (if x<2662 then (if x<2650 then 2 else (if x<2652 then 0 else 4)) else (if x<2702 then 0 else (if x<2710 then 0 else 2))) else (if x<2772 then (if x<2738 then 4 else (if x<2762 then 0 else 4)) else (if x<2792 then 3 else (if x<2800 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8187 : Finset ℕ := ([1650,1652,1702,1752,2650,2652,2702,2732,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8187 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8187 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8187 4 (fun x => (if x<2652 then (if x<1702 then (if x<1652 then 0 else 1) else (if x<1752 then 0 else (if x<2650 then 1 else 0))) else (if x<2732 then (if x<2702 then 1 else 0) else (if x<2772 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8188 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1764,2618,2620,2650,2652,2662,2702,2710,2732,2738,2762,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8188 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8188 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8188 1590 4
  · have he : independentCachedBranchMembers8188.erase 1590=independentCachedBranchMembers8186 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8186
  · have he : independentCachedBranchMembers8188.filter (independentCachedEdge 1590)=independentCachedBranchMembers8187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8187
def independentCachedBranchMembers8189 : Finset ℕ := ([1642,1650,1692,1702,1734,1764,2618,2650,2702,2710,2732,2772] : List ℕ).toFinset
theorem independentCachedBranchBound8189 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8189 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8189 4 (fun x => (if x<2618 then (if x<1702 then (if x<1650 then 0 else (if x<1692 then 1 else 2)) else (if x<1734 then 0 else (if x<1764 then 1 else 2))) else (if x<2710 then (if x<2650 then 1 else (if x<2702 then 0 else 1)) else (if x<2732 then 0 else (if x<2772 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8190 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2702,2710,2732,2738,2762,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8190 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8190 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8190 1762 4
  · have he : independentCachedBranchMembers8190.erase 1762=independentCachedBranchMembers8188 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8188
  · have he : independentCachedBranchMembers8190.filter (independentCachedEdge 1762)=independentCachedBranchMembers8189 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8189
def independentCachedBranchMembers8191 : Finset ℕ := ([1644,1652,1692,1720,1752,1764,2620,2652,2732,2772,2792,2800] : List ℕ).toFinset
theorem independentCachedBranchBound8191 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8191 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8191 4 (fun x => (if x<2620 then (if x<1720 then (if x<1652 then 0 else (if x<1692 then 1 else 0)) else (if x<1752 then 1 else (if x<1764 then 2 else 2))) else (if x<2772 then (if x<2652 then 0 else (if x<2732 then 3 else 3)) else (if x<2792 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
