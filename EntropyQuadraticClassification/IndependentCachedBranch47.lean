/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch46
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4288 : Finset ℕ := ([40,66,130,222,1626,1644,1652,1708,1734,1768,2620,2646,2680,2762,2770,3132,3150,3158,3192,3214,3222,3256,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4288 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4288 5 (fun x => (if x<2680 then (if x<1652 then (if x<222 then (if x<66 then 0 else (if x<130 then 0 else 1)) else (if x<1626 then 1 else (if x<1644 then 2 else 2))) else (if x<1768 then (if x<1708 then 3 else (if x<1734 then 0 else 0)) else (if x<2620 then 3 else (if x<2646 then 0 else 0)))) else (if x<3192 then (if x<3132 then (if x<2762 then 2 else (if x<2770 then 1 else 2)) else (if x<3150 then 4 else (if x<3158 then 4 else 3))) else (if x<3256 then (if x<3214 then 3 else (if x<3222 then 1 else 4)) else (if x<3282 then (if x<3274 then 0 else 3) else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4289 : Finset ℕ := ([18,36,40,66,130,222,1596,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1764,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,2800,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4289 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4289 1764 5
  · have he : independentCachedBranchMembers4289.erase 1764=independentCachedBranchMembers4287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4287
  · have he : independentCachedBranchMembers4289.filter (independentCachedEdge 1764)=independentCachedBranchMembers4288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4288
def independentCachedBranchMembers4290 : Finset ℕ := ([18,36,40,130,1626,1644,1678,1720,1734,1738,2680,2714,2732,2770,3132,3150,3188,3192,3222,3226,3244,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4290 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4290 5 (fun x => (if x<2732 then (if x<1678 then (if x<130 then (if x<36 then 0 else (if x<40 then 0 else 1)) else (if x<1626 then 1 else (if x<1644 then 0 else 0))) else (if x<1738 then (if x<1720 then 2 else (if x<1734 then 2 else 1)) else (if x<2680 then 3 else (if x<2714 then 1 else 0)))) else (if x<3222 then (if x<3150 then (if x<2770 then 0 else (if x<3132 then 1 else 1)) else (if x<3188 then 2 else (if x<3192 then 3 else 2))) else (if x<3282 then (if x<3226 then 1 else (if x<3244 then 2 else 2)) else (if x<3300 then 0 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4291 : Finset ℕ := ([18,1626,1678,2680,2732,2770,3132,3150,3222,3226,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4291 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4291 4 (fun x => (if x<3132 then (if x<2680 then (if x<1626 then 0 else (if x<1678 then 0 else 1)) else (if x<2732 then 1 else (if x<2770 then 0 else 2))) else (if x<3226 then (if x<3150 then 2 else (if x<3222 then 3 else 1)) else (if x<3300 then 2 else (if x<3304 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4292 : Finset ℕ := ([18,36,40,130,1626,1644,1678,1720,1734,1738,2620,2680,2714,2732,2770,3132,3150,3188,3192,3222,3226,3244,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4292 2620 4
  · have he : independentCachedBranchMembers4292.erase 2620=independentCachedBranchMembers4290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4290
  · have he : independentCachedBranchMembers4292.filter (independentCachedEdge 2620)=independentCachedBranchMembers4291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4291
def independentCachedBranchMembers4293 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1764,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,2800,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4293 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4293 1614 5
  · have he : independentCachedBranchMembers4293.erase 1614=independentCachedBranchMembers4289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4289
  · have he : independentCachedBranchMembers4293.filter (independentCachedEdge 1614)=independentCachedBranchMembers4292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4292
def independentCachedBranchMembers4294 : Finset ℕ := ([36,40,66,130,1644,1652,1708,1720,1734,1738,1746,2668,2680,2732,2740,2758,2762,2770,3132,3150,3158,3162,3214,3222,3226,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4294 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4294 5 (fun x => (if x<2732 then (if x<1708 then (if x<130 then (if x<40 then 0 else (if x<66 then 1 else 0)) else (if x<1644 then 1 else (if x<1652 then 1 else 2))) else (if x<1738 then (if x<1720 then 0 else (if x<1734 then 2 else 1)) else (if x<2668 then (if x<1746 then 0 else 2) else (if x<2680 then 3 else 1)))) else (if x<3158 then (if x<2762 then (if x<2740 then 4 else (if x<2758 then 0 else 3)) else (if x<3132 then (if x<2770 then 4 else 0) else (if x<3150 then 0 else 3))) else (if x<3222 then (if x<3162 then 2 else (if x<3214 then 0 else 4)) else (if x<3300 then (if x<3226 then 1 else 2) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4295 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1764,1768,2620,2646,2668,2680,2714,2732,2740,2758,2762,2770,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4295 3102 5
  · have he : independentCachedBranchMembers4295.erase 3102=independentCachedBranchMembers4293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4293
  · have he : independentCachedBranchMembers4295.filter (independentCachedEdge 3102)=independentCachedBranchMembers4294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4294
def independentCachedBranchMembers4296 : Finset ℕ := ([36,66,1626,1708,1720,1738,2646,2668,2680,2714,2740,2758,2770,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4296 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4296 5 (fun x => (if x<2758 then (if x<1738 then (if x<1626 then (if x<66 then 0 else 0) else (if x<1708 then 0 else (if x<1720 then 1 else 2))) else (if x<2680 then (if x<2646 then 1 else (if x<2668 then 2 else 3)) else (if x<2714 then 2 else (if x<2740 then 2 else 0)))) else (if x<3188 then (if x<3132 then (if x<2770 then 3 else 0) else (if x<3150 then 1 else (if x<3162 then 3 else 1))) else (if x<3256 then (if x<3222 then 4 else (if x<3244 then 3 else 0)) else (if x<3274 then 4 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4297 : Finset ℕ := ([66,1738,2758,2770,3150,3162,3188,3222,3244,3256] : List ℕ).toFinset
theorem independentCachedBranchBound4297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4297 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4297 4 (fun x => (if x<3162 then (if x<2758 then (if x<1738 then 0 else 0) else (if x<2770 then 0 else (if x<3150 then 1 else 0))) else (if x<3222 then (if x<3188 then 1 else 2) else (if x<3244 then 1 else (if x<3256 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4298 : Finset ℕ := ([36,66,1626,1652,1708,1720,1738,2646,2668,2680,2714,2740,2758,2770,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4298 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4298 1652 4
  · have he : independentCachedBranchMembers4298.erase 1652=independentCachedBranchMembers4296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4296
  · have he : independentCachedBranchMembers4298.filter (independentCachedEdge 1652)=independentCachedBranchMembers4297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4297
def independentCachedBranchMembers4299 : Finset ℕ := ([36,66,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4299 4 (fun x => (if x<3188 then (if x<3132 then (if x<66 then 0 else 0) else (if x<3150 then 0 else (if x<3162 then 1 else 0))) else (if x<3256 then (if x<3222 then 1 else (if x<3244 then 1 else 1)) else (if x<3274 then 2 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4300 : Finset ℕ := ([36,66,1626,1652,1686,1708,1720,1738,2646,2668,2680,2714,2740,2758,2770,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4300 1686 4
  · have he : independentCachedBranchMembers4300.erase 1686=independentCachedBranchMembers4298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4298
  · have he : independentCachedBranchMembers4300.filter (independentCachedEdge 1686)=independentCachedBranchMembers4299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4299
def independentCachedBranchMembers4301 : Finset ℕ := ([1652,1708,1720,1738,2646,2714,3132,3150,3162,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4301 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4301 4 (fun x => (if x<2714 then (if x<1720 then (if x<1708 then 0 else 0) else (if x<1738 then 1 else (if x<2646 then 1 else 0))) else (if x<3162 then (if x<3132 then 1 else (if x<3150 then 2 else 2)) else (if x<3222 then 3 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4302 : Finset ℕ := ([36,66,1596,1626,1652,1686,1708,1720,1738,2646,2668,2680,2714,2740,2758,2770,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4302 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4302 1596 4
  · have he : independentCachedBranchMembers4302.erase 1596=independentCachedBranchMembers4300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4300
  · have he : independentCachedBranchMembers4302.filter (independentCachedEdge 1596)=independentCachedBranchMembers4301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4301
def independentCachedBranchMembers4303 : Finset ℕ := ([66,1626,1652,1708,2646,2680,2770,3132,3150,3222,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4303 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4303 4 (fun x => (if x<2770 then (if x<1708 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<2646 then 1 else (if x<2680 then 0 else 2))) else (if x<3222 then (if x<3132 then 2 else (if x<3150 then 1 else 0)) else (if x<3274 then (if x<3256 then 2 else 3) else (if x<3300 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4304 : Finset ℕ := ([36,66,1596,1626,1652,1686,1708,1720,1738,1764,2646,2668,2680,2714,2740,2758,2770,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4304 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4304 1764 4
  · have he : independentCachedBranchMembers4304.erase 1764=independentCachedBranchMembers4302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4302
  · have he : independentCachedBranchMembers4304.filter (independentCachedEdge 1764)=independentCachedBranchMembers4303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4303
def independentCachedBranchMembers4305 : Finset ℕ := ([36,1626,1720,1738,2680,2714,2770,3132,3150,3188,3222,3244,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4305 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4305 4 (fun x => (if x<2770 then (if x<1738 then (if x<1626 then 0 else (if x<1720 then 0 else 1)) else (if x<2680 then 1 else (if x<2714 then 2 else 0))) else (if x<3188 then (if x<3132 then 2 else (if x<3150 then 1 else 1)) else (if x<3244 then (if x<3222 then 3 else 2) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4306 : Finset ℕ := ([36,66,1596,1614,1626,1652,1686,1708,1720,1738,1764,2646,2668,2680,2714,2740,2758,2770,3132,3150,3162,3188,3222,3244,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4306 1614 4
  · have he : independentCachedBranchMembers4306.erase 1614=independentCachedBranchMembers4304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4304
  · have he : independentCachedBranchMembers4306.filter (independentCachedEdge 1614)=independentCachedBranchMembers4305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4305
def independentCachedBranchMembers4307 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1764,1768,2620,2646,2668,2680,2710,2714,2732,2740,2758,2762,2770,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4307 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4307 2710 5
  · have he : independentCachedBranchMembers4307.erase 2710=independentCachedBranchMembers4295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4295
  · have he : independentCachedBranchMembers4307.filter (independentCachedEdge 2710)=independentCachedBranchMembers4306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4306
def independentCachedBranchMembers4308 : Finset ℕ := ([40,130,1626,1644,1652,1686,1720,1734,2646,2680,2714,2732,2740,2762,2770,3132,3162,3180,3188,3214,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4308 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4308 5 (fun x => (if x<2740 then (if x<1720 then (if x<1644 then (if x<130 then 0 else (if x<1626 then 0 else 1)) else (if x<1652 then 0 else (if x<1686 then 1 else 1))) else (if x<2680 then (if x<1734 then 1 else (if x<2646 then 0 else 1)) else (if x<2714 then 0 else (if x<2732 then 1 else 2)))) else (if x<3188 then (if x<3132 then (if x<2762 then 1 else (if x<2770 then 2 else 0)) else (if x<3162 then 0 else (if x<3180 then 2 else 3))) else (if x<3256 then (if x<3214 then 4 else (if x<3222 then 2 else 0)) else (if x<3270 then 3 else (if x<3304 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4309 : Finset ℕ := ([1644,1652,1720,1734,2646,2714,3132,3162,3214,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4309 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4309 4 (fun x => (if x<2714 then (if x<1720 then (if x<1652 then 0 else 1) else (if x<1734 then 0 else (if x<2646 then 1 else 1))) else (if x<3214 then (if x<3132 then 0 else (if x<3162 then 2 else 2)) else (if x<3222 then 2 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4310 : Finset ℕ := ([40,130,1596,1626,1644,1652,1686,1720,1734,2646,2680,2714,2732,2740,2762,2770,3132,3162,3180,3188,3214,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4310 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4310 1596 4
  · have he : independentCachedBranchMembers4310.erase 1596=independentCachedBranchMembers4308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4308
  · have he : independentCachedBranchMembers4310.filter (independentCachedEdge 1596)=independentCachedBranchMembers4309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4309
def independentCachedBranchMembers4311 : Finset ℕ := ([130,1644,1686,1720,2714,2740,2770,3132,3162,3188,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4311 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4311 4 (fun x => (if x<2770 then (if x<1720 then (if x<1644 then 0 else (if x<1686 then 0 else 1)) else (if x<2714 then 1 else (if x<2740 then 0 else 1))) else (if x<3188 then (if x<3132 then 2 else (if x<3162 then 2 else 2)) else (if x<3270 then 0 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4312 : Finset ℕ := ([1644,1720,2740,2770,3188,3270] : List ℕ).toFinset
theorem independentCachedBranchBound4312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4312 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4312 3 (fun x => (if x<2770 then (if x<1720 then 0 else (if x<2740 then 0 else 1)) else (if x<3188 then 1 else (if x<3270 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4313 : Finset ℕ := ([130,1644,1686,1720,2714,2740,2770,3132,3162,3188,3214,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4313 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4313 3214 3
  · have he : independentCachedBranchMembers4313.erase 3214=independentCachedBranchMembers4311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4311
  · have he : independentCachedBranchMembers4313.filter (independentCachedEdge 3214)=independentCachedBranchMembers4312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4312
def independentCachedBranchMembers4314 : Finset ℕ := ([40,130,1596,1626,1644,1652,1686,1720,1734,1768,2646,2680,2714,2732,2740,2762,2770,3132,3162,3180,3188,3214,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4314 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4314 1768 4
  · have he : independentCachedBranchMembers4314.erase 1768=independentCachedBranchMembers4310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4310
  · have he : independentCachedBranchMembers4314.filter (independentCachedEdge 1768)=independentCachedBranchMembers4313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4313
def independentCachedBranchMembers4315 : Finset ℕ := ([40,1652,1686,1734,2646,2740,2770,3132,3162,3180,3214,3256,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4315 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4315 4 (fun x => (if x<2770 then (if x<1734 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<2646 then 1 else (if x<2740 then 0 else 2))) else (if x<3180 then (if x<3132 then 2 else (if x<3162 then 1 else 2)) else (if x<3256 then (if x<3214 then 3 else 1) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4316 : Finset ℕ := ([40,130,1596,1626,1644,1652,1678,1686,1720,1734,1768,2646,2680,2714,2732,2740,2762,2770,3132,3162,3180,3188,3214,3222,3256,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4316 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4316 1678 4
  · have he : independentCachedBranchMembers4316.erase 1678=independentCachedBranchMembers4314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4314
  · have he : independentCachedBranchMembers4316.filter (independentCachedEdge 1678)=independentCachedBranchMembers4315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4315
def independentCachedBranchMembers4317 : Finset ℕ := ([18,36,40,66,130,222,1596,1614,1626,1644,1652,1678,1686,1708,1720,1734,1738,1746,1764,1768,2620,2646,2650,2668,2680,2710,2714,2732,2740,2758,2762,2770,2800,3102,3132,3150,3158,3162,3180,3188,3192,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4317 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4317 2650 5
  · have he : independentCachedBranchMembers4317.erase 2650=independentCachedBranchMembers4307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4307
  · have he : independentCachedBranchMembers4317.filter (independentCachedEdge 2650)=independentCachedBranchMembers4316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4316
def independentCachedBranchMembers4318 : Finset ℕ := ([40,66,1626,1644,1678,1686,1720,1738,1746,1764,2646,2680,2714,2732,2740,2758,3132,3150,3192,3226,3244,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4318 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4318 5 (fun x => (if x<2714 then (if x<1720 then (if x<1644 then (if x<66 then 0 else (if x<1626 then 0 else 1)) else (if x<1678 then 1 else (if x<1686 then 1 else 2))) else (if x<1764 then (if x<1738 then 0 else (if x<1746 then 2 else 0)) else (if x<2646 then 2 else (if x<2680 then 0 else 1)))) else (if x<3192 then (if x<2758 then (if x<2732 then 1 else (if x<2740 then 1 else 2)) else (if x<3132 then 2 else (if x<3150 then 3 else 3))) else (if x<3252 then (if x<3226 then 4 else (if x<3244 then 3 else 0)) else (if x<3270 then 4 else (if x<3304 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4319 : Finset ℕ := ([40,66,1626,1644,1686,1738,2680,2740,3132,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound4319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4319 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4319 4 (fun x => (if x<2680 then (if x<1644 then (if x<66 then 0 else (if x<1626 then 0 else 1)) else (if x<1686 then 1 else (if x<1738 then 2 else 2))) else (if x<3226 then (if x<2740 then 1 else (if x<3132 then 2 else 0)) else (if x<3244 then 3 else (if x<3270 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
