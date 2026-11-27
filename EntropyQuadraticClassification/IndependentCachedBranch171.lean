/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch170
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8256 : Finset ℕ := ([72,80,130,132,1614,1622,1642,1644,1650,1652,1690,1692,1702,2650,2652,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8256 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8256 3250 4
  · have he : independentCachedBranchMembers8256.erase 3250=independentCachedBranchMembers8252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8252
  · have he : independentCachedBranchMembers8256.filter (independentCachedEdge 3250)=independentCachedBranchMembers8255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8255
def independentCachedBranchMembers8257 : Finset ℕ := ([130,1614,1642,1652,1690,2652,2662,2680,2710,2732,2738,3162,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8257 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8257 4 (fun x => (if x<2680 then (if x<1652 then (if x<1614 then 0 else (if x<1642 then 1 else 2)) else (if x<2652 then (if x<1690 then 0 else 1) else (if x<2662 then 0 else 1))) else (if x<3162 then (if x<2732 then (if x<2710 then 2 else 3) else (if x<2738 then 3 else 1)) else (if x<3242 then (if x<3214 then 2 else 3) else (if x<3252 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8258 : Finset ℕ := ([1652,1690,2662,2732,3214,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8258 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8258 3 (fun x => (if x<2732 then (if x<1690 then 0 else (if x<2662 then 1 else 0)) else (if x<3214 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8259 : Finset ℕ := ([72,130,1614,1642,1652,1690,2652,2662,2680,2710,2732,2738,3162,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8259 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8259 72 3
  · have he : independentCachedBranchMembers8259.erase 72=independentCachedBranchMembers8257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8257
  · have he : independentCachedBranchMembers8259.filter (independentCachedEdge 72)=independentCachedBranchMembers8258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8258
def independentCachedBranchMembers8260 : Finset ℕ := ([72,80,130,132,1614,1622,1642,1644,1650,1652,1690,1692,1702,2650,2652,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8260 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8260 3244 4
  · have he : independentCachedBranchMembers8260.erase 3244=independentCachedBranchMembers8256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8256
  · have he : independentCachedBranchMembers8260.filter (independentCachedEdge 3244)=independentCachedBranchMembers8259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8259
def independentCachedBranchMembers8261 : Finset ℕ := ([72,80,130,132,1614,1622,1690,1692,2650,2652,2702,2710,3162,3164,3214,3222] : List ℕ).toFinset
theorem independentCachedBranchBound8261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8261 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8261 4 (fun x => (if x<2650 then (if x<1614 then (if x<130 then (if x<80 then 0 else 1) else (if x<132 then 0 else 1)) else (if x<1690 then (if x<1622 then 2 else 3) else (if x<1692 then 2 else 3))) else (if x<3162 then (if x<2702 then (if x<2652 then 1 else 0) else (if x<2710 then 1 else 0)) else (if x<3214 then (if x<3164 then 2 else 3) else (if x<3222 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8262 : Finset ℕ := ([72,80,130,132,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,2650,2652,2662,2680,2702,2710,2732,2738,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8262 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8262 1720 4
  · have he : independentCachedBranchMembers8262.erase 1720=independentCachedBranchMembers8260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8260
  · have he : independentCachedBranchMembers8262.filter (independentCachedEdge 1720)=independentCachedBranchMembers8261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8261
def independentCachedBranchMembers8263 : Finset ℕ := ([40,48,72,80,130,132,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8263 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8263 192 5
  · have he : independentCachedBranchMembers8263.erase 192=independentCachedBranchMembers8241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8241
  · have he : independentCachedBranchMembers8263.filter (independentCachedEdge 192)=independentCachedBranchMembers8262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8262
def independentCachedBranchMembers8264 : Finset ℕ := ([80,252,1582,1614,1652,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2702,2762,2772,2800,3132,3164,3174,3192,3214,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8264 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8264 5 (fun x => (if x<2662 then (if x<1702 then (if x<1614 then (if x<252 then 0 else (if x<1582 then 0 else 1)) else (if x<1652 then 2 else (if x<1692 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1734 then 3 else 1)) else (if x<2620 then (if x<1762 then 0 else 3) else (if x<2652 then 1 else 0)))) else (if x<3164 then (if x<2762 then (if x<2680 then 1 else (if x<2702 then 4 else 1)) else (if x<2800 then (if x<2772 then 4 else 1) else (if x<3132 then 0 else 3))) else (if x<3214 then (if x<3174 then 2 else (if x<3192 then 2 else 0)) else (if x<3252 then (if x<3242 then 2 else 3) else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8265 : Finset ℕ := ([252,1582,1614,1692,1720,1752,2662,2772,2800,3174,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8265 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8265 4 (fun x => (if x<2662 then (if x<1692 then (if x<1582 then 0 else (if x<1614 then 1 else 2)) else (if x<1720 then 0 else (if x<1752 then 1 else 2))) else (if x<3174 then (if x<2772 then 1 else (if x<2800 then 0 else 1)) else (if x<3252 then 2 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8266 : Finset ℕ := ([80,130,252,1582,1614,1652,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2702,2762,2772,2800,3132,3164,3174,3192,3214,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8266 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8266 130 4
  · have he : independentCachedBranchMembers8266.erase 130=independentCachedBranchMembers8264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8264
  · have he : independentCachedBranchMembers8266.filter (independentCachedEdge 130)=independentCachedBranchMembers8265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8265
def independentCachedBranchMembers8267 : Finset ℕ := ([80,1582,1692,1702,1752,1762,2652,2662,2772,3164,3174,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8267 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8267 4 (fun x => (if x<2652 then (if x<1702 then (if x<1582 then 0 else (if x<1692 then 0 else 1)) else (if x<1752 then 1 else (if x<1762 then 2 else 2))) else (if x<3164 then (if x<2662 then 1 else (if x<2772 then 1 else 0)) else (if x<3174 then 2 else (if x<3242 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8268 : Finset ℕ := ([48,80,130,252,1582,1614,1652,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2702,2762,2772,2800,3132,3164,3174,3192,3214,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8268 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8268 48 4
  · have he : independentCachedBranchMembers8268.erase 48=independentCachedBranchMembers8266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8266
  · have he : independentCachedBranchMembers8268.filter (independentCachedEdge 48)=independentCachedBranchMembers8267 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8267
def independentCachedBranchMembers8269 : Finset ℕ := ([130,1614,1702,1720,1762,2620,2662,2680,2702,2762,2772,3164,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8269 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8269 4 (fun x => (if x<2680 then (if x<1720 then (if x<1614 then 0 else (if x<1702 then 1 else 0)) else (if x<2620 then (if x<1762 then 2 else 1) else (if x<2662 then 2 else 1))) else (if x<3164 then (if x<2762 then (if x<2702 then 0 else 3) else (if x<2772 then 1 else 3)) else (if x<3252 then (if x<3242 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8270 : Finset ℕ := ([1702,1762,2662,2772,3164,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8270 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8270 3 (fun x => (if x<2772 then (if x<1762 then 0 else (if x<2662 then 1 else 0)) else (if x<3164 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8271 : Finset ℕ := ([48,130,1614,1702,1720,1762,2620,2662,2680,2702,2762,2772,3164,3242,3252,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8271 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8271 48 3
  · have he : independentCachedBranchMembers8271.erase 48=independentCachedBranchMembers8269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8269
  · have he : independentCachedBranchMembers8271.filter (independentCachedEdge 48)=independentCachedBranchMembers8270 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8270
def independentCachedBranchMembers8272 : Finset ℕ := ([48,80,130,252,1582,1614,1652,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2702,2762,2772,2800,3132,3164,3174,3192,3214,3242,3252,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8272 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8272 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8272 3284 4
  · have he : independentCachedBranchMembers8272.erase 3284=independentCachedBranchMembers8268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8268
  · have he : independentCachedBranchMembers8272.filter (independentCachedEdge 3284)=independentCachedBranchMembers8271 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8271
def independentCachedBranchMembers8273 : Finset ℕ := ([252,1582,1692,1702,1720,2652,2662,2680,2762,2772,2800,3132,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8273 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8273 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8273 4 (fun x => (if x<2680 then (if x<1702 then (if x<1582 then 0 else (if x<1692 then 1 else 0)) else (if x<2652 then (if x<1720 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3132 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<2800 then 3 else 1)) else (if x<3242 then (if x<3214 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8274 : Finset ℕ := ([1692,1720,2662,2762,3132,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8274 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8274 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8274 3 (fun x => (if x<2762 then (if x<1720 then 0 else (if x<2662 then 1 else 0)) else (if x<3132 then 2 else (if x<3252 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8275 : Finset ℕ := ([80,252,1582,1692,1702,1720,2652,2662,2680,2762,2772,2800,3132,3214,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8275 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8275 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8275 80 3
  · have he : independentCachedBranchMembers8275.erase 80=independentCachedBranchMembers8273 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8273
  · have he : independentCachedBranchMembers8275.filter (independentCachedEdge 80)=independentCachedBranchMembers8274 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8274
def independentCachedBranchMembers8276 : Finset ℕ := ([48,80,130,252,1582,1614,1652,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2702,2762,2772,2800,3132,3164,3174,3192,3214,3242,3252,3274,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8276 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8276 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8276 3274 4
  · have he : independentCachedBranchMembers8276.erase 3274=independentCachedBranchMembers8272 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8272
  · have he : independentCachedBranchMembers8276.filter (independentCachedEdge 3274)=independentCachedBranchMembers8275 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8275
def independentCachedBranchMembers8277 : Finset ℕ := ([48,80,130,252,1582,1614,1692,1762,2620,2652,2702,2800,3132,3164,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8277 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8277 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8277 4 (fun x => (if x<2620 then (if x<1582 then (if x<130 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1692 then (if x<1614 then 2 else 3) else (if x<1762 then 2 else 3))) else (if x<3132 then (if x<2702 then (if x<2652 then 0 else 1) else (if x<2800 then 0 else 1)) else (if x<3214 then (if x<3164 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8278 : Finset ℕ := ([48,80,130,252,1582,1614,1642,1652,1692,1702,1720,1734,1752,1762,2620,2652,2662,2680,2702,2762,2772,2800,3132,3164,3174,3192,3214,3242,3252,3274,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8278 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8278 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8278 1642 4
  · have he : independentCachedBranchMembers8278.erase 1642=independentCachedBranchMembers8276 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8276
  · have he : independentCachedBranchMembers8278.filter (independentCachedEdge 1642)=independentCachedBranchMembers8277 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8277
def independentCachedBranchMembers8279 : Finset ℕ := ([18,40,48,72,80,130,132,192,222,250,252,1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2618,2620,2650,2652,2662,2680,2702,2710,2732,2738,2762,2764,2770,2772,2792,2800,3072,3102,3130,3132,3162,3164,3174,3192,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8279 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8279 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8279 18 5
  · have he : independentCachedBranchMembers8279.erase 18=independentCachedBranchMembers8263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8263
  · have he : independentCachedBranchMembers8279.filter (independentCachedEdge 18)=independentCachedBranchMembers8278 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8278
def independentCachedBranchMembers8280 : Finset ℕ := ([72,250,1590,1622,1642,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2710,2762,2772,2792,3130,3162,3174,3192,3222,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8280 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8280 5 (fun x => (if x<2662 then (if x<1702 then (if x<1622 then (if x<250 then 0 else (if x<1590 then 0 else 1)) else (if x<1642 then 2 else (if x<1690 then 0 else 1))) else (if x<1752 then (if x<1720 then 2 else (if x<1734 then 3 else 1)) else (if x<2618 then (if x<1764 then 0 else 3) else (if x<2650 then 1 else 0)))) else (if x<3162 then (if x<2762 then (if x<2680 then 1 else (if x<2710 then 4 else 1)) else (if x<2792 then (if x<2772 then 1 else 4) else (if x<3130 then 0 else 3))) else (if x<3222 then (if x<3174 then 2 else (if x<3192 then 2 else 0)) else (if x<3252 then (if x<3242 then 2 else 2) else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8281 : Finset ℕ := ([250,1590,1622,1690,1720,1752,2662,2762,2792,3174,3242,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8281 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8281 4 (fun x => (if x<2662 then (if x<1690 then (if x<1590 then 0 else (if x<1622 then 1 else 2)) else (if x<1720 then 0 else (if x<1752 then 1 else 2))) else (if x<3174 then (if x<2762 then 1 else (if x<2792 then 0 else 1)) else (if x<3242 then 2 else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8282 : Finset ℕ := ([72,132,250,1590,1622,1642,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2710,2762,2772,2792,3130,3162,3174,3192,3222,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8282 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8282 132 4
  · have he : independentCachedBranchMembers8282.erase 132=independentCachedBranchMembers8280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8280
  · have he : independentCachedBranchMembers8282.filter (independentCachedEdge 132)=independentCachedBranchMembers8281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8281
def independentCachedBranchMembers8283 : Finset ℕ := ([72,1590,1690,1702,1752,1764,2650,2662,2762,3162,3174,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8283 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8283 4 (fun x => (if x<2650 then (if x<1702 then (if x<1590 then 0 else (if x<1690 then 0 else 1)) else (if x<1752 then 1 else (if x<1764 then 2 else 2))) else (if x<3162 then (if x<2662 then 1 else (if x<2762 then 1 else 0)) else (if x<3174 then 2 else (if x<3252 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8284 : Finset ℕ := ([40,72,132,250,1590,1622,1642,1690,1702,1720,1734,1752,1764,2618,2650,2662,2680,2710,2762,2772,2792,3130,3162,3174,3192,3222,3242,3252,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8284 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8284 40 4
  · have he : independentCachedBranchMembers8284.erase 40=independentCachedBranchMembers8282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8282
  · have he : independentCachedBranchMembers8284.filter (independentCachedEdge 40)=independentCachedBranchMembers8283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8283
def independentCachedBranchMembers8285 : Finset ℕ := ([250,1590,1690,1702,1720,2650,2662,2680,2762,2772,2792,3130,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8285 4 (fun x => (if x<2680 then (if x<1702 then (if x<1590 then 0 else (if x<1690 then 1 else 0)) else (if x<2650 then (if x<1720 then 2 else 1) else (if x<2662 then 0 else 1))) else (if x<3130 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<2792 then 3 else 1)) else (if x<3242 then (if x<3222 then 0 else 2) else (if x<3252 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8286 : Finset ℕ := ([1690,1720,2662,2772,3130,3242] : List ℕ).toFinset
theorem independentCachedBranchBound8286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8286 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8286 3 (fun x => (if x<2772 then (if x<1720 then 0 else (if x<2662 then 1 else 0)) else (if x<3130 then 2 else (if x<3242 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8287 : Finset ℕ := ([72,250,1590,1690,1702,1720,2650,2662,2680,2762,2772,2792,3130,3222,3242,3252] : List ℕ).toFinset
theorem independentCachedBranchBound8287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8287 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8287 72 3
  · have he : independentCachedBranchMembers8287.erase 72=independentCachedBranchMembers8285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8285
  · have he : independentCachedBranchMembers8287.filter (independentCachedEdge 72)=independentCachedBranchMembers8286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8286
end EntropyDesigns.QuadraticRefinement
