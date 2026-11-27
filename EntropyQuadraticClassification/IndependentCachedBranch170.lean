/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch169
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8224 : Finset ℕ := ([48,252,1582,1590,1644,1650,1652,1720,1762,1764,2618,2620,2662,2680,2732,2738,2792,2800,3130,3132,3174,3192,3242,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8224 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8224 5 (fun x => (if x<2680 then (if x<1652 then (if x<1590 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1644 then 2 else (if x<1650 then 2 else 1))) else (if x<1764 then (if x<1720 then 0 else (if x<1762 then 0 else 2)) else (if x<2620 then (if x<2618 then 1 else 1) else (if x<2662 then 0 else 1)))) else (if x<3132 then (if x<2792 then (if x<2732 then 3 else (if x<2738 then 1 else 2)) else (if x<2800 then 2 else (if x<3130 then 0 else 3))) else (if x<3242 then (if x<3174 then 4 else (if x<3192 then 4 else 0)) else (if x<3304 then (if x<3252 then 4 else 0) else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8225 : Finset ℕ := ([48,252,1582,1644,1650,1762,2620,2732,2738,2800,3132,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8225 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8225 4 (fun x => (if x<2620 then (if x<1644 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1650 then 2 else (if x<1762 then 1 else 2))) else (if x<2800 then (if x<2732 then 0 else (if x<2738 then 1 else 2)) else (if x<3132 then 0 else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8226 : Finset ℕ := ([48,252,1582,1590,1642,1644,1650,1652,1720,1762,1764,2618,2620,2662,2680,2732,2738,2792,2800,3130,3132,3174,3192,3242,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8226 1642 4
  · have he : independentCachedBranchMembers8226.erase 1642=independentCachedBranchMembers8224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8224
  · have he : independentCachedBranchMembers8226.filter (independentCachedEdge 1642)=independentCachedBranchMembers8225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8225
def independentCachedBranchMembers8227 : Finset ℕ := ([252,1582,1590,1644,1652,1764,2620,2662,2732,3132,3174,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8227 4 (fun x => (if x<2620 then (if x<1644 then (if x<1582 then 0 else (if x<1590 then 1 else 2)) else (if x<1652 then 0 else (if x<1764 then 1 else 2))) else (if x<3132 then (if x<2662 then 0 else (if x<2732 then 1 else 3)) else (if x<3174 then 3 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8228 : Finset ℕ := ([48,250,252,1582,1590,1642,1644,1650,1652,1720,1762,1764,2618,2620,2662,2680,2732,2738,2792,2800,3130,3132,3174,3192,3242,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8228 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8228 250 4
  · have he : independentCachedBranchMembers8228.erase 250=independentCachedBranchMembers8226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8226
  · have he : independentCachedBranchMembers8228.filter (independentCachedEdge 250)=independentCachedBranchMembers8227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8227
def independentCachedBranchMembers8229 : Finset ℕ := ([48,1590,1650,1652,1762,1764,2662,2738,2800,3174,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8229 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8229 4 (fun x => (if x<2662 then (if x<1652 then (if x<1590 then 0 else (if x<1650 then 0 else 1)) else (if x<1762 then 2 else (if x<1764 then 2 else 1))) else (if x<3174 then (if x<2738 then 1 else (if x<2800 then 0 else 1)) else (if x<3252 then 2 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8230 : Finset ℕ := ([40,48,250,252,1582,1590,1642,1644,1650,1652,1720,1762,1764,2618,2620,2662,2680,2732,2738,2792,2800,3130,3132,3174,3192,3242,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8230 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8230 40 4
  · have he : independentCachedBranchMembers8230.erase 40=independentCachedBranchMembers8228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8228
  · have he : independentCachedBranchMembers8230.filter (independentCachedEdge 40)=independentCachedBranchMembers8229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8229
def independentCachedBranchMembers8231 : Finset ℕ := ([252,1582,1642,1652,1764,2620,2662,2680,2732,2738,2792,3130,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8231 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8231 4 (fun x => (if x<2680 then (if x<1652 then (if x<1582 then 0 else (if x<1642 then 1 else 2)) else (if x<2620 then (if x<1764 then 0 else 1) else (if x<2662 then 0 else 1))) else (if x<3130 then (if x<2738 then (if x<2732 then 2 else 1) else (if x<2792 then 3 else 3)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8232 : Finset ℕ := ([1652,1764,2662,2738,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8232 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8232 3 (fun x => (if x<2738 then (if x<1764 then 0 else (if x<2662 then 1 else 0)) else (if x<3252 then 2 else (if x<3312 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8233 : Finset ℕ := ([40,252,1582,1642,1652,1764,2620,2662,2680,2732,2738,2792,3130,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8233 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8233 40 3
  · have he : independentCachedBranchMembers8233.erase 40=independentCachedBranchMembers8231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8231
  · have he : independentCachedBranchMembers8233.filter (independentCachedEdge 40)=independentCachedBranchMembers8232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8232
def independentCachedBranchMembers8234 : Finset ℕ := ([40,48,250,252,1582,1590,1642,1644,1650,1652,1720,1762,1764,2618,2620,2662,2680,2732,2738,2792,2800,3130,3132,3174,3192,3242,3250,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8234 3250 4
  · have he : independentCachedBranchMembers8234.erase 3250=independentCachedBranchMembers8230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8230
  · have he : independentCachedBranchMembers8234.filter (independentCachedEdge 3250)=independentCachedBranchMembers8233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8233
def independentCachedBranchMembers8235 : Finset ℕ := ([250,1590,1642,1652,1762,2618,2662,2680,2732,2738,2800,3132,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8235 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8235 4 (fun x => (if x<2680 then (if x<1652 then (if x<1590 then 0 else (if x<1642 then 1 else 0)) else (if x<2618 then (if x<1762 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3132 then (if x<2738 then (if x<2732 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3252 then (if x<3242 then 2 else 0) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8236 : Finset ℕ := ([1642,1762,2662,2732,3242,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8236 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8236 3 (fun x => (if x<2732 then (if x<1762 then 0 else (if x<2662 then 1 else 0)) else (if x<3242 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8237 : Finset ℕ := ([48,250,1590,1642,1652,1762,2618,2662,2680,2732,2738,2800,3132,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8237 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8237 48 3
  · have he : independentCachedBranchMembers8237.erase 48=independentCachedBranchMembers8235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8235
  · have he : independentCachedBranchMembers8237.filter (independentCachedEdge 48)=independentCachedBranchMembers8236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8236
def independentCachedBranchMembers8238 : Finset ℕ := ([40,48,250,252,1582,1590,1642,1644,1650,1652,1720,1762,1764,2618,2620,2662,2680,2732,2738,2792,2800,3130,3132,3174,3192,3242,3244,3250,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8238 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8238 3244 4
  · have he : independentCachedBranchMembers8238.erase 3244=independentCachedBranchMembers8234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8234
  · have he : independentCachedBranchMembers8238.filter (independentCachedEdge 3244)=independentCachedBranchMembers8237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8237
def independentCachedBranchMembers8239 : Finset ℕ := ([40,48,250,252,1582,1590,1762,1764,2618,2620,2792,2800,3130,3132,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8239 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8239 4 (fun x => (if x<2618 then (if x<1582 then (if x<250 then (if x<48 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1762 then (if x<1590 then 2 else 3) else (if x<1764 then 2 else 3))) else (if x<3130 then (if x<2792 then (if x<2620 then 0 else 1) else (if x<2800 then 0 else 1)) else (if x<3304 then (if x<3132 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8240 : Finset ℕ := ([40,48,250,252,1582,1590,1642,1644,1650,1652,1702,1720,1762,1764,2618,2620,2662,2680,2732,2738,2792,2800,3130,3132,3174,3192,3242,3244,3250,3252,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8240 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8240 1702 4
  · have he : independentCachedBranchMembers8240.erase 1702=independentCachedBranchMembers8238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8238
  · have he : independentCachedBranchMembers8240.filter (independentCachedEdge 1702)=independentCachedBranchMembers8239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8239
def independentCachedBranchMembers8241 : Finset ℕ := ([40,48,72,80,130,132,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8241 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8241 222 5
  · have he : independentCachedBranchMembers8241.erase 222=independentCachedBranchMembers8223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8223
  · have he : independentCachedBranchMembers8241.filter (independentCachedEdge 222)=independentCachedBranchMembers8240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8240
def independentCachedBranchMembers8242 : Finset ℕ := ([80,132,1614,1622,1642,1650,1652,1690,1692,1702,2650,2662,2680,2702,2732,2738,3162,3164,3174,3192,3214,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8242 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8242 5 (fun x => (if x<2680 then (if x<1652 then (if x<1622 then (if x<132 then 0 else (if x<1614 then 0 else 1)) else (if x<1642 then 2 else (if x<1650 then 2 else 0))) else (if x<1702 then (if x<1690 then 1 else (if x<1692 then 2 else 1)) else (if x<2650 then 0 else (if x<2662 then 0 else 1)))) else (if x<3174 then (if x<2738 then (if x<2702 then 3 else (if x<2732 then 0 else 3)) else (if x<3162 then 3 else (if x<3164 then 2 else 4))) else (if x<3222 then (if x<3192 then 2 else (if x<3214 then 0 else 4)) else (if x<3242 then 2 else (if x<3252 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8243 : Finset ℕ := ([80,1614,1650,1652,2680,2702,2738,3162,3164,3174,3222,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8243 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8243 4 (fun x => (if x<2738 then (if x<1652 then (if x<1614 then 0 else (if x<1650 then 1 else 0)) else (if x<2680 then 1 else (if x<2702 then 0 else 1))) else (if x<3174 then (if x<3162 then 2 else (if x<3164 then 0 else 2)) else (if x<3222 then 3 else (if x<3242 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8244 : Finset ℕ := ([80,132,1614,1622,1642,1650,1652,1690,1692,1702,2650,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8244 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8244 2710 4
  · have he : independentCachedBranchMembers8244.erase 2710=independentCachedBranchMembers8242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8242
  · have he : independentCachedBranchMembers8244.filter (independentCachedEdge 2710)=independentCachedBranchMembers8243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8243
def independentCachedBranchMembers8245 : Finset ℕ := ([132,1642,1650,1690,2650,2680,2738,3164,3174,3214,3222,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8245 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8245 4 (fun x => (if x<2738 then (if x<1690 then (if x<1642 then 0 else (if x<1650 then 0 else 1)) else (if x<2650 then 1 else (if x<2680 then 0 else 2))) else (if x<3214 then (if x<3164 then 1 else (if x<3174 then 2 else 3)) else (if x<3222 then 2 else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8246 : Finset ℕ := ([80,132,1614,1622,1642,1650,1652,1690,1692,1702,2650,2652,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8246 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8246 2652 4
  · have he : independentCachedBranchMembers8246.erase 2652=independentCachedBranchMembers8244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8244
  · have he : independentCachedBranchMembers8246.filter (independentCachedEdge 2652)=independentCachedBranchMembers8245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8245
def independentCachedBranchMembers8247 : Finset ℕ := ([80,132,1614,1642,1652,1690,2650,2702,3162,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8247 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8247 4 (fun x => (if x<2650 then (if x<1642 then (if x<132 then 0 else (if x<1614 then 0 else 1)) else (if x<1652 then 2 else (if x<1690 then 1 else 2))) else (if x<3214 then (if x<2702 then 0 else (if x<3162 then 0 else 2)) else (if x<3242 then 1 else (if x<3252 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8248 : Finset ℕ := ([80,132,1614,1622,1642,1644,1650,1652,1690,1692,1702,2650,2652,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8248 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8248 1644 4
  · have he : independentCachedBranchMembers8248.erase 1644=independentCachedBranchMembers8246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8246
  · have he : independentCachedBranchMembers8248.filter (independentCachedEdge 1644)=independentCachedBranchMembers8247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8247
def independentCachedBranchMembers8249 : Finset ℕ := ([132,1614,1622,1642,1650,1692,2650,2662,2732,3162,3174,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8249 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8249 4 (fun x => (if x<2650 then (if x<1642 then (if x<1614 then 0 else (if x<1622 then 1 else 2)) else (if x<1650 then 0 else (if x<1692 then 1 else 2))) else (if x<3162 then (if x<2662 then 0 else (if x<2732 then 1 else 2)) else (if x<3174 then 3 else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8250 : Finset ℕ := ([80,130,132,1614,1622,1642,1644,1650,1652,1690,1692,1702,2650,2652,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8250 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8250 130 4
  · have he : independentCachedBranchMembers8250.erase 130=independentCachedBranchMembers8248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8248
  · have he : independentCachedBranchMembers8250.filter (independentCachedEdge 130)=independentCachedBranchMembers8249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8249
def independentCachedBranchMembers8251 : Finset ℕ := ([80,1622,1650,1652,1690,1692,2662,2702,2732,3174,3214,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8251 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8251 4 (fun x => (if x<2662 then (if x<1652 then (if x<1622 then 0 else (if x<1650 then 0 else 1)) else (if x<1690 then 2 else (if x<1692 then 1 else 2))) else (if x<3174 then (if x<2702 then 1 else (if x<2732 then 1 else 0)) else (if x<3214 then 2 else (if x<3242 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8252 : Finset ℕ := ([72,80,130,132,1614,1622,1642,1644,1650,1652,1690,1692,1702,2650,2652,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8252 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8252 72 4
  · have he : independentCachedBranchMembers8252.erase 72=independentCachedBranchMembers8250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8250
  · have he : independentCachedBranchMembers8252.filter (independentCachedEdge 72)=independentCachedBranchMembers8251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8251
def independentCachedBranchMembers8253 : Finset ℕ := ([132,1622,1642,1652,1692,2650,2662,2680,2702,2732,2738,3164,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8253 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8253 4 (fun x => (if x<2680 then (if x<1652 then (if x<1622 then 0 else (if x<1642 then 1 else 0)) else (if x<2650 then (if x<1692 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3164 then (if x<2732 then (if x<2702 then 2 else 3) else (if x<2738 then 1 else 3)) else (if x<3242 then (if x<3222 then 2 else 3) else (if x<3252 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8254 : Finset ℕ := ([1642,1692,2662,2738,3222,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8254 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8254 3 (fun x => (if x<2738 then (if x<1692 then 0 else (if x<2662 then 1 else 0)) else (if x<3222 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8255 : Finset ℕ := ([80,132,1622,1642,1652,1692,2650,2662,2680,2702,2732,2738,3164,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8255 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8255 80 3
  · have he : independentCachedBranchMembers8255.erase 80=independentCachedBranchMembers8253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8253
  · have he : independentCachedBranchMembers8255.filter (independentCachedEdge 80)=independentCachedBranchMembers8254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8254
end EntropyDesigns.QuadraticRefinement
