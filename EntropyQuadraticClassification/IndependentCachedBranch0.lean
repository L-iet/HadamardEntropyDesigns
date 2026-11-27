/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedGraph
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers0 : Finset ℕ := ([1594,1628,1678,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3226,3238,3252,3256,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound0 : ListCliqueBound independentCachedEdge independentCachedBranchMembers0 7 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers0 7 (fun x => (if x<2772 then (if x<2650 then (if x<1768 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1746 then 0 else 0)) else (if x<2620 then (if x<2614 then 0 else 1) else (if x<2638 then 2 else 1))) else (if x<2716 then (if x<2680 then (if x<2662 then 2 else 2) else (if x<2710 then 1 else 2)) else (if x<2732 then (if x<2730 then 1 else 1) else (if x<2738 then 3 else (if x<2762 then 3 else 3))))) else (if x<3188 then (if x<3118 then (if x<2800 then (if x<2788 then 3 else 1) else (if x<3102 then 2 else 4)) else (if x<3178 then (if x<3158 then 5 else 5) else (if x<3180 then 4 else (if x<3186 then 6 else 6)))) else (if x<3256 then (if x<3238 then (if x<3226 then 4 else 5) else (if x<3252 then 4 else 3)) else (if x<3276 then (if x<3270 then 4 else 6) else (if x<3288 then 3 else (if x<3298 then 6 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1 : Finset ℕ := ([1594,1768,2614,2650,2710,2762,2772,2788,3102,3118,3178,3180,3186,3188,3238,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound1 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1 6 (fun x => (if x<3118 then (if x<2710 then (if x<2614 then (if x<1768 then 0 else 0) else (if x<2650 then 0 else 1)) else (if x<2772 then (if x<2762 then 1 else 2) else (if x<2788 then 2 else (if x<3102 then 0 else 0)))) else (if x<3188 then (if x<3180 then (if x<3178 then 3 else 1) else (if x<3186 then 4 else 3)) else (if x<3256 then (if x<3238 then 2 else 1) else (if x<3276 then 3 else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2 : Finset ℕ := ([1594,1628,1678,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3226,3238,3252,3256,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2 1720 6
  · have he : independentCachedBranchMembers2.erase 1720=independentCachedBranchMembers0 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound0
  · have he : independentCachedBranchMembers2.filter (independentCachedEdge 1720)=independentCachedBranchMembers1 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1
def independentCachedBranchMembers3 : Finset ℕ := ([1628,1678,2620,2638,2716,2762,2772,2800,3102,3158,3178,3180,3186,3188,3226,3238,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound3 : ListCliqueBound independentCachedEdge independentCachedBranchMembers3 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers3 6 (fun x => (if x<3158 then (if x<2716 then (if x<2620 then (if x<1678 then 0 else 0) else (if x<2638 then 1 else 0)) else (if x<2772 then (if x<2762 then 0 else 2) else (if x<2800 then 1 else (if x<3102 then 2 else 0)))) else (if x<3188 then (if x<3180 then (if x<3178 then 3 else 3) else (if x<3186 then 4 else 4)) else (if x<3238 then (if x<3226 then 1 else 3) else (if x<3256 then 3 else (if x<3276 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4 : Finset ℕ := ([1594,1628,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3226,3238,3252,3256,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4 1702 6
  · have he : independentCachedBranchMembers4.erase 1702=independentCachedBranchMembers2 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2
  · have he : independentCachedBranchMembers4.filter (independentCachedEdge 1702)=independentCachedBranchMembers3 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound3
def independentCachedBranchMembers5 : Finset ℕ := ([1628,1678,2638,2650,2710,2716,2732,2738,3102,3118,3178,3188,3238,3256,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5 6 (fun x => (if x<3118 then (if x<2710 then (if x<2638 then (if x<1678 then 0 else 0) else (if x<2650 then 0 else 1)) else (if x<2732 then (if x<2716 then 1 else 0) else (if x<2738 then 2 else (if x<3102 then 2 else 0)))) else (if x<3256 then (if x<3188 then (if x<3178 then 3 else 1) else (if x<3238 then 3 else 1)) else (if x<3276 then (if x<3270 then 2 else 3) else (if x<3288 then 0 else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6 : Finset ℕ := ([1594,1628,1652,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3226,3238,3252,3256,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6 1652 6
  · have he : independentCachedBranchMembers6.erase 1652=independentCachedBranchMembers4 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4
  · have he : independentCachedBranchMembers6.filter (independentCachedEdge 1652)=independentCachedBranchMembers5 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5
def independentCachedBranchMembers7 : Finset ℕ := ([1594,1768,2614,2620,2732,2738,2788,2800,3102,3158,3178,3188,3226,3238,3256,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound7 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7 6 (fun x => (if x<3158 then (if x<2732 then (if x<2614 then (if x<1768 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2788 then (if x<2738 then 2 else 1) else (if x<2800 then 0 else (if x<3102 then 2 else 0)))) else (if x<3238 then (if x<3188 then (if x<3178 then 3 else 3) else (if x<3226 then 4 else 3)) else (if x<3270 then (if x<3256 then 3 else 1) else (if x<3276 then 4 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3226,3238,3252,3256,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8 1642 6
  · have he : independentCachedBranchMembers8.erase 1642=independentCachedBranchMembers6 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6
  · have he : independentCachedBranchMembers8.filter (independentCachedEdge 1642)=independentCachedBranchMembers7 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7
def independentCachedBranchMembers9 : Finset ℕ := ([1746,2614,2638,2662,2680,2716,2730,2732,2738,2762,2772,2788,3178,3180,3186,3188,3238,3256,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound9 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9 6 (fun x => (if x<2772 then (if x<2716 then (if x<2638 then (if x<2614 then 0 else 1) else (if x<2662 then 1 else (if x<2680 then 2 else 1))) else (if x<2732 then (if x<2730 then 1 else 1) else (if x<2738 then 0 else (if x<2762 then 0 else 0)))) else (if x<3188 then (if x<3178 then (if x<2788 then 0 else 1) else (if x<3180 then 2 else (if x<3186 then 3 else 3))) else (if x<3256 then (if x<3238 then 2 else 2) else (if x<3270 then 2 else (if x<3288 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3252,3256,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound10 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10 3192 6
  · have he : independentCachedBranchMembers10.erase 3192=independentCachedBranchMembers8 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8
  · have he : independentCachedBranchMembers10.filter (independentCachedEdge 3192)=independentCachedBranchMembers9 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9
def independentCachedBranchMembers11 : Finset ℕ := ([1678,1702,1720,1768,2614,2620,2638,2650,2662,2680,2732,2738,2762,2772,3118,3158,3178,3188,3252,3270,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound11 : ListCliqueBound independentCachedEdge independentCachedBranchMembers11 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers11 6 (fun x => (if x<2738 then (if x<2620 then (if x<1720 then (if x<1702 then 0 else 1) else (if x<1768 then 0 else (if x<2614 then 1 else 1))) else (if x<2662 then (if x<2638 then 2 else (if x<2650 then 0 else 2)) else (if x<2680 then 2 else (if x<2732 then 0 else 0)))) else (if x<3178 then (if x<2772 then (if x<2762 then 2 else 3) else (if x<3118 then 2 else (if x<3158 then 4 else 4))) else (if x<3270 then (if x<3188 then 3 else (if x<3252 then 3 else 4)) else (if x<3276 then 3 else (if x<3288 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers12 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3252,3256,3270,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound12 : ListCliqueBound independentCachedEdge independentCachedBranchMembers12 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers12 3284 6
  · have he : independentCachedBranchMembers12.erase 3284=independentCachedBranchMembers10 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10
  · have he : independentCachedBranchMembers12.filter (independentCachedEdge 3284)=independentCachedBranchMembers11 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound11
def independentCachedBranchMembers13 : Finset ℕ := ([1594,1628,1702,1720,2662,2680,2710,2716,2732,2738,2762,2772,2788,2800,3178,3188,3226,3252,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound13 : ListCliqueBound independentCachedEdge independentCachedBranchMembers13 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers13 6 (fun x => (if x<2772 then (if x<2680 then (if x<1702 then (if x<1628 then 0 else 0) else (if x<1720 then 1 else (if x<2662 then 1 else 1))) else (if x<2732 then (if x<2710 then 0 else (if x<2716 then 2 else 3)) else (if x<2738 then 1 else (if x<2762 then 0 else 2)))) else (if x<3226 then (if x<2800 then (if x<2788 then 0 else 2) else (if x<3178 then 3 else (if x<3188 then 4 else 4))) else (if x<3276 then (if x<3252 then 2 else (if x<3270 then 2 else 2)) else (if x<3288 then 4 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers14 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound14 : ListCliqueBound independentCachedEdge independentCachedBranchMembers14 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers14 3274 6
  · have he : independentCachedBranchMembers14.erase 3274=independentCachedBranchMembers12 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound12
  · have he : independentCachedBranchMembers14.filter (independentCachedEdge 3274)=independentCachedBranchMembers13 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound13
def independentCachedBranchMembers15 : Finset ℕ := ([1642,1652,1678,1768,2620,2650,2662,2680,2716,2732,2738,2762,2772,2788,3180,3186,3226,3238,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound15 : ListCliqueBound independentCachedEdge independentCachedBranchMembers15 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers15 6 (fun x => (if x<2762 then (if x<2650 then (if x<1678 then (if x<1652 then 0 else 0) else (if x<1768 then 1 else (if x<2620 then 1 else 2))) else (if x<2716 then (if x<2662 then 2 else (if x<2680 then 0 else 0)) else (if x<2732 then 3 else (if x<2738 then 1 else 2)))) else (if x<3226 then (if x<2788 then (if x<2772 then 0 else 0) else (if x<3180 then 3 else (if x<3186 then 4 else 4))) else (if x<3256 then (if x<3238 then 3 else (if x<3252 then 4 else 2)) else (if x<3276 then 4 else (if x<3298 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers16 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound16 : ListCliqueBound independentCachedEdge independentCachedBranchMembers16 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers16 3250 6
  · have he : independentCachedBranchMembers16.erase 3250=independentCachedBranchMembers14 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound14
  · have he : independentCachedBranchMembers16.filter (independentCachedEdge 3250)=independentCachedBranchMembers15 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound15
def independentCachedBranchMembers17 : Finset ℕ := ([1594,1628,1642,1652,2614,2638,2662,2680,2710,2732,2738,2762,2772,2800,3118,3158,3180,3186,3238,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound17 : ListCliqueBound independentCachedEdge independentCachedBranchMembers17 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers17 6 (fun x => (if x<2762 then (if x<2638 then (if x<1642 then (if x<1628 then 0 else 0) else (if x<1652 then 1 else (if x<2614 then 1 else 2))) else (if x<2710 then (if x<2662 then 2 else (if x<2680 then 1 else 0)) else (if x<2732 then 3 else (if x<2738 then 2 else 0)))) else (if x<3180 then (if x<2800 then (if x<2772 then 1 else 0) else (if x<3118 then 3 else (if x<3158 then 2 else 2))) else (if x<3252 then (if x<3186 then 4 else (if x<3238 then 4 else 4)) else (if x<3256 then 2 else (if x<3276 then 4 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers18 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound18 : ListCliqueBound independentCachedEdge independentCachedBranchMembers18 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers18 3244 6
  · have he : independentCachedBranchMembers18.erase 3244=independentCachedBranchMembers16 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound16
  · have he : independentCachedBranchMembers18.filter (independentCachedEdge 3244)=independentCachedBranchMembers17 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound17
def independentCachedBranchMembers19 : Finset ℕ := ([1594,1628,1678,1768,2620,2650,2662,2680,2710,2730,2800,3102,3118,3158,3178,3188,3192,3226,3238,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound19 : ListCliqueBound independentCachedEdge independentCachedBranchMembers19 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers19 6 (fun x => (if x<3102 then (if x<2650 then (if x<1678 then (if x<1628 then 0 else 0) else (if x<1768 then 0 else (if x<2620 then 0 else 1))) else (if x<2710 then (if x<2662 then 1 else (if x<2680 then 1 else 0)) else (if x<2730 then 1 else (if x<2800 then 0 else 1)))) else (if x<3226 then (if x<3178 then (if x<3118 then 2 else (if x<3158 then 3 else 3)) else (if x<3188 then 2 else (if x<3192 then 2 else 3))) else (if x<3256 then (if x<3238 then 3 else (if x<3252 then 2 else 3)) else (if x<3276 then 2 else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers20 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound20 : ListCliqueBound independentCachedEdge independentCachedBranchMembers20 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers20 1740 6
  · have he : independentCachedBranchMembers20.erase 1740=independentCachedBranchMembers18 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound18
  · have he : independentCachedBranchMembers20.filter (independentCachedEdge 1740)=independentCachedBranchMembers19 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound19
def independentCachedBranchMembers21 : Finset ℕ := ([1594,1642,1652,1678,2614,2650,2662,2680,2716,2762,2772,2800,3102,3158,3178,3180,3186,3188,3244,3250,3252,3270,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound21 : ListCliqueBound independentCachedEdge independentCachedBranchMembers21 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers21 6 (fun x => (if x<3102 then (if x<2662 then (if x<1678 then (if x<1642 then 0 else (if x<1652 then 1 else 0)) else (if x<2614 then 1 else (if x<2650 then 0 else 2))) else (if x<2762 then (if x<2680 then 2 else (if x<2716 then 0 else 1)) else (if x<2772 then 1 else (if x<2800 then 0 else 2)))) else (if x<3244 then (if x<3180 then (if x<3158 then 3 else (if x<3178 then 4 else 3)) else (if x<3186 then 4 else (if x<3188 then 2 else 3))) else (if x<3270 then (if x<3250 then 3 else (if x<3252 then 3 else 4)) else (if x<3288 then 3 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers22 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2762,2772,2776,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound22 : ListCliqueBound independentCachedEdge independentCachedBranchMembers22 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers22 2776 6
  · have he : independentCachedBranchMembers22.erase 2776=independentCachedBranchMembers20 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound20
  · have he : independentCachedBranchMembers22.filter (independentCachedEdge 2776)=independentCachedBranchMembers21 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound21
def independentCachedBranchMembers23 : Finset ℕ := ([1628,1642,1652,1768,2620,2638,2662,2680,2710,2762,2772,2788,3102,3118,3178,3180,3186,3188,3226,3244,3250,3252,3270,3288] : List ℕ).toFinset
theorem independentCachedBranchBound23 : ListCliqueBound independentCachedEdge independentCachedBranchMembers23 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers23 6 (fun x => (if x<3102 then (if x<2662 then (if x<1768 then (if x<1642 then 0 else (if x<1652 then 0 else 1)) else (if x<2620 then 1 else (if x<2638 then 2 else 0))) else (if x<2762 then (if x<2680 then 2 else (if x<2710 then 0 else 2)) else (if x<2772 then 1 else (if x<2788 then 0 else 1)))) else (if x<3226 then (if x<3180 then (if x<3118 then 3 else (if x<3178 then 4 else 3)) else (if x<3186 then 2 else (if x<3188 then 4 else 3))) else (if x<3252 then (if x<3244 then 4 else (if x<3250 then 3 else 3)) else (if x<3270 then 4 else (if x<3288 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers24 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2662,2680,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound24 : ListCliqueBound independentCachedEdge independentCachedBranchMembers24 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers24 2758 6
  · have he : independentCachedBranchMembers24.erase 2758=independentCachedBranchMembers22 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound22
  · have he : independentCachedBranchMembers24.filter (independentCachedEdge 2758)=independentCachedBranchMembers23 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound23
def independentCachedBranchMembers25 : Finset ℕ := ([1628,1702,1720,1768,2614,2650,2662,2680,2716,2732,2738,2800,3102,3118,3180,3186,3226,3238,3252,3256,3270,3274,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound25 : ListCliqueBound independentCachedEdge independentCachedBranchMembers25 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers25 6 (fun x => (if x<3102 then (if x<2662 then (if x<1768 then (if x<1702 then 0 else (if x<1720 then 1 else 0)) else (if x<2614 then 1 else (if x<2650 then 1 else 2))) else (if x<2732 then (if x<2680 then 2 else (if x<2716 then 0 else 0)) else (if x<2738 then 1 else (if x<2800 then 0 else 2)))) else (if x<3252 then (if x<3186 then (if x<3118 then 3 else (if x<3180 then 4 else 3)) else (if x<3226 then 2 else (if x<3238 then 4 else 3))) else (if x<3274 then (if x<3256 then 4 else (if x<3270 then 3 else 4)) else (if x<3284 then 3 else (if x<3288 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers26 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2662,2674,2680,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound26 : ListCliqueBound independentCachedEdge independentCachedBranchMembers26 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers26 2674 6
  · have he : independentCachedBranchMembers26.erase 2674=independentCachedBranchMembers24 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound24
  · have he : independentCachedBranchMembers26.filter (independentCachedEdge 2674)=independentCachedBranchMembers25 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound25
def independentCachedBranchMembers27 : Finset ℕ := ([1594,1678,1702,1720,2620,2638,2662,2680,2710,2732,2738,2788,3102,3158,3180,3186,3238,3252,3256,3270,3274,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound27 : ListCliqueBound independentCachedEdge independentCachedBranchMembers27 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers27 6 (fun x => (if x<3102 then (if x<2662 then (if x<1720 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<2620 then 1 else (if x<2638 then 2 else 2))) else (if x<2732 then (if x<2680 then 1 else (if x<2710 then 0 else 2)) else (if x<2738 then 1 else (if x<2788 then 1 else 2)))) else (if x<3256 then (if x<3186 then (if x<3158 then 2 else (if x<3180 then 3 else 2)) else (if x<3238 then 0 else (if x<3252 then 3 else 2))) else (if x<3284 then (if x<3270 then 4 else (if x<3274 then 0 else 3)) else (if x<3288 then 4 else (if x<3298 then 5 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers28 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2662,2668,2674,2680,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound28 : ListCliqueBound independentCachedEdge independentCachedBranchMembers28 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers28 2668 6
  · have he : independentCachedBranchMembers28.erase 2668=independentCachedBranchMembers26 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound26
  · have he : independentCachedBranchMembers28.filter (independentCachedEdge 2668)=independentCachedBranchMembers27 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound27
def independentCachedBranchMembers29 : Finset ℕ := ([1594,1628,1652,1678,1702,1746,1768,2614,2668,2680,2710,2730,2732,2762,2776,2788,2800,3118,3186,3188,3226,3238,3250,3252,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound29 : ListCliqueBound independentCachedEdge independentCachedBranchMembers29 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers29 6 (fun x => (if x<2762 then (if x<1768 then (if x<1678 then (if x<1628 then 0 else (if x<1652 then 0 else 1)) else (if x<1702 then 0 else (if x<1746 then 1 else 0))) else (if x<2680 then (if x<2614 then 0 else (if x<2668 then 1 else 2)) else (if x<2730 then (if x<2710 then 1 else 3) else (if x<2732 then 1 else 3)))) else (if x<3188 then (if x<2800 then (if x<2776 then 2 else (if x<2788 then 3 else 1)) else (if x<3118 then 2 else (if x<3186 then 4 else 4))) else (if x<3250 then (if x<3226 then 2 else (if x<3238 then 4 else 3)) else (if x<3270 then (if x<3252 then 5 else 4) else (if x<3284 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers30 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2662,2668,2674,2680,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound30 : ListCliqueBound independentCachedEdge independentCachedBranchMembers30 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers30 2792 6
  · have he : independentCachedBranchMembers30.erase 2792=independentCachedBranchMembers28 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound28
  · have he : independentCachedBranchMembers30.filter (independentCachedEdge 2792)=independentCachedBranchMembers29 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound29
def independentCachedBranchMembers31 : Finset ℕ := ([1594,1628,1642,1678,1720,1746,1768,2638,2674,2680,2710,2716,2730,2732,2758,2762,2800,3158,3178,3180,3250,3252,3256,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound31 : ListCliqueBound independentCachedEdge independentCachedBranchMembers31 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers31 6 (fun x => (if x<2732 then (if x<1768 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 0 else (if x<1746 then 1 else 0))) else (if x<2680 then (if x<2638 then 0 else (if x<2674 then 1 else 2)) else (if x<2716 then (if x<2710 then 1 else 2) else (if x<2730 then 1 else 1)))) else (if x<3180 then (if x<2800 then (if x<2758 then 3 else (if x<2762 then 3 else 2)) else (if x<3158 then 3 else (if x<3178 then 4 else 2))) else (if x<3256 then (if x<3250 then 4 else (if x<3252 then 5 else 4)) else (if x<3288 then (if x<3284 then 3 else 5) else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers32 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound32 : ListCliqueBound independentCachedEdge independentCachedBranchMembers32 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers32 2702 6
  · have he : independentCachedBranchMembers32.erase 2702=independentCachedBranchMembers30 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound30
  · have he : independentCachedBranchMembers32.filter (independentCachedEdge 2702)=independentCachedBranchMembers31 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound31
def independentCachedBranchMembers33 : Finset ℕ := ([1594,1628,1642,1678,1720,1746,1768,2620,2638,2650,2668,2680,2716,2730,2738,2772,2776,3118,3178,3186,3226,3244,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound33 : ListCliqueBound independentCachedEdge independentCachedBranchMembers33 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers33 6 (fun x => (if x<2730 then (if x<1768 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<1720 then 0 else (if x<1746 then 1 else 0))) else (if x<2650 then (if x<2620 then 0 else (if x<2638 then 2 else 1)) else (if x<2680 then (if x<2668 then 2 else 3) else (if x<2716 then 1 else 1)))) else (if x<3186 then (if x<2776 then (if x<2738 then 1 else (if x<2772 then 2 else 2)) else (if x<3118 then 3 else (if x<3178 then 3 else 4))) else (if x<3252 then (if x<3226 then 5 else (if x<3244 then 3 else 4)) else (if x<3270 then (if x<3256 then 2 else 5) else (if x<3274 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers34 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound34 : ListCliqueBound independentCachedEdge independentCachedBranchMembers34 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers34 2652 6
  · have he : independentCachedBranchMembers34.erase 2652=independentCachedBranchMembers32 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound32
  · have he : independentCachedBranchMembers34.filter (independentCachedEdge 2652)=independentCachedBranchMembers33 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound33
def independentCachedBranchMembers35 : Finset ℕ := ([1594,1628,1652,1678,1702,1746,1768,2614,2620,2650,2674,2680,2730,2738,2758,2772,2788,3158,3180,3188,3238,3244,3252,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound35 : ListCliqueBound independentCachedEdge independentCachedBranchMembers35 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers35 6 (fun x => (if x<2738 then (if x<1768 then (if x<1678 then (if x<1628 then 0 else (if x<1652 then 0 else 1)) else (if x<1702 then 0 else (if x<1746 then 1 else 0))) else (if x<2650 then (if x<2614 then 0 else (if x<2620 then 1 else 2)) else (if x<2680 then (if x<2674 then 2 else 3) else (if x<2730 then 1 else 1)))) else (if x<3188 then (if x<2788 then (if x<2758 then 2 else (if x<2772 then 3 else 2)) else (if x<3158 then 1 else (if x<3180 then 3 else 4))) else (if x<3252 then (if x<3238 then 5 else (if x<3244 then 4 else 5)) else (if x<3288 then (if x<3274 then 2 else 4) else (if x<3298 then 5 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers36 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound36 : ListCliqueBound independentCachedEdge independentCachedBranchMembers36 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers36 2618 6
  · have he : independentCachedBranchMembers36.erase 2618=independentCachedBranchMembers34 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound34
  · have he : independentCachedBranchMembers36.filter (independentCachedEdge 2618)=independentCachedBranchMembers35 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound35
def independentCachedBranchMembers37 : Finset ℕ := ([1652,1678,1720,1746,1768,2614,2618,2650,2652,2662,2668,2710,2716,2730,2732,2758,2762,2800,3158,3178,3226,3238,3244,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound37 : ListCliqueBound independentCachedEdge independentCachedBranchMembers37 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers37 6 (fun x => (if x<2716 then (if x<2618 then (if x<1746 then (if x<1678 then 0 else (if x<1720 then 1 else 0)) else (if x<1768 then 0 else (if x<2614 then 1 else 2))) else (if x<2662 then (if x<2650 then 3 else (if x<2652 then 2 else 3)) else (if x<2668 then 3 else (if x<2710 then 2 else 1)))) else (if x<3158 then (if x<2758 then (if x<2730 then 2 else (if x<2732 then 1 else 3)) else (if x<2762 then 2 else (if x<2800 then 3 else 0))) else (if x<3238 then (if x<3178 then 4 else (if x<3226 then 4 else 4)) else (if x<3274 then (if x<3244 then 4 else 5) else (if x<3276 then 5 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers38 : Finset ℕ := ([1652,1768,2614,2650,2652,2668,2716,2730,2732,2758,2800,3158,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound38 : ListCliqueBound independentCachedEdge independentCachedBranchMembers38 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers38 5 (fun x => (if x<2730 then (if x<2650 then (if x<1768 then 0 else (if x<2614 then 0 else 0)) else (if x<2668 then (if x<2652 then 1 else 2) else (if x<2716 then 0 else 1))) else (if x<3158 then (if x<2758 then (if x<2732 then 0 else 2) else (if x<2800 then 1 else 0)) else (if x<3274 then (if x<3238 then 2 else 2) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers39 : Finset ℕ := ([1652,1678,1720,1746,1768,2614,2618,2650,2652,2662,2668,2710,2716,2730,2732,2758,2762,2800,3158,3178,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound39 : ListCliqueBound independentCachedEdge independentCachedBranchMembers39 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers39 3270 5
  · have he : independentCachedBranchMembers39.erase 3270=independentCachedBranchMembers37 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound37
  · have he : independentCachedBranchMembers39.filter (independentCachedEdge 3270)=independentCachedBranchMembers38 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound38
def independentCachedBranchMembers40 : Finset ℕ := ([1678,1720,2614,2618,2650,2668,2716,2730,2758,2762,2800,3178,3226,3244,3276] : List ℕ).toFinset
theorem independentCachedBranchBound40 : ListCliqueBound independentCachedEdge independentCachedBranchMembers40 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers40 5 (fun x => (if x<2730 then (if x<2618 then (if x<1720 then 0 else (if x<2614 then 0 else 1)) else (if x<2668 then (if x<2650 then 2 else 1) else (if x<2716 then 1 else 0))) else (if x<3178 then (if x<2762 then (if x<2758 then 0 else 0) else (if x<2800 then 2 else 0)) else (if x<3244 then (if x<3226 then 2 else 2) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers41 : Finset ℕ := ([1652,1678,1720,1746,1768,2614,2618,2650,2652,2662,2668,2710,2716,2730,2732,2758,2762,2800,3158,3178,3180,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound41 : ListCliqueBound independentCachedEdge independentCachedBranchMembers41 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers41 3180 5
  · have he : independentCachedBranchMembers41.erase 3180=independentCachedBranchMembers39 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound39
  · have he : independentCachedBranchMembers41.filter (independentCachedEdge 3180)=independentCachedBranchMembers40 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound40
def independentCachedBranchMembers42 : Finset ℕ := ([1678,1768,2614,2618,2652,2668,2716,2732,2758,2762,3158,3178,3226,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound42 : ListCliqueBound independentCachedEdge independentCachedBranchMembers42 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers42 5 (fun x => (if x<2732 then (if x<2618 then (if x<1768 then 0 else (if x<2614 then 0 else 1)) else (if x<2668 then (if x<2652 then 2 else 1) else (if x<2716 then 2 else 2))) else (if x<3178 then (if x<2762 then (if x<2758 then 0 else 1) else (if x<3158 then 0 else 1)) else (if x<3238 then (if x<3226 then 2 else 2) else (if x<3276 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers43 : Finset ℕ := ([1652,1678,1720,1746,1768,2614,2618,2620,2650,2652,2662,2668,2710,2716,2730,2732,2758,2762,2800,3158,3178,3180,3226,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound43 : ListCliqueBound independentCachedEdge independentCachedBranchMembers43 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers43 2620 5
  · have he : independentCachedBranchMembers43.erase 2620=independentCachedBranchMembers41 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound41
  · have he : independentCachedBranchMembers43.filter (independentCachedEdge 2620)=independentCachedBranchMembers42 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound42
def independentCachedBranchMembers44 : Finset ℕ := ([1594,1628,1642,1652,1678,1702,1720,1740,1746,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound44 : ListCliqueBound independentCachedEdge independentCachedBranchMembers44 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers44 1776 6
  · have he : independentCachedBranchMembers44.erase 1776=independentCachedBranchMembers36 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound36
  · have he : independentCachedBranchMembers44.filter (independentCachedEdge 1776)=independentCachedBranchMembers43 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound43
def independentCachedBranchMembers45 : Finset ℕ := ([1642,1678,1702,1746,1768,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2776,2788,2800,3118,3188,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound45 : ListCliqueBound independentCachedEdge independentCachedBranchMembers45 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers45 6 (fun x => (if x<2732 then (if x<2620 then (if x<1746 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<1768 then 0 else (if x<2618 then 1 else 2))) else (if x<2662 then (if x<2638 then 3 else (if x<2652 then 2 else 4)) else (if x<2710 then (if x<2674 then 3 else 0) else (if x<2730 then 0 else 1)))) else (if x<3188 then (if x<2788 then (if x<2762 then 2 else (if x<2776 then 0 else 1)) else (if x<2800 then 1 else (if x<3118 then 3 else 2))) else (if x<3274 then (if x<3244 then 3 else (if x<3256 then 5 else 2)) else (if x<3288 then (if x<3276 then 5 else 2) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers46 : Finset ℕ := ([1702,1768,2620,2638,2652,2674,2710,2730,2762,2776,2788,3188,3244,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound46 : ListCliqueBound independentCachedEdge independentCachedBranchMembers46 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers46 5 (fun x => (if x<2730 then (if x<2638 then (if x<1768 then 0 else (if x<2620 then 0 else 1)) else (if x<2674 then (if x<2652 then 1 else 2) else (if x<2710 then 1 else 0))) else (if x<3188 then (if x<2776 then (if x<2762 then 0 else 2) else (if x<2788 then 0 else 0)) else (if x<3276 then (if x<3244 then 2 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers47 : Finset ℕ := ([1642,1678,1702,1746,1768,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2776,2788,2800,3118,3186,3188,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound47 : ListCliqueBound independentCachedEdge independentCachedBranchMembers47 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers47 3186 5
  · have he : independentCachedBranchMembers47.erase 3186=independentCachedBranchMembers45 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound45
  · have he : independentCachedBranchMembers47.filter (independentCachedEdge 3186)=independentCachedBranchMembers46 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound46
def independentCachedBranchMembers48 : Finset ℕ := ([1678,1768,2618,2638,2652,2674,2732,2762,2776,2788,3118,3188,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound48 : ListCliqueBound independentCachedEdge independentCachedBranchMembers48 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers48 5 (fun x => (if x<2762 then (if x<2638 then (if x<1768 then 0 else (if x<2618 then 0 else 1)) else (if x<2674 then (if x<2652 then 1 else 2) else (if x<2732 then 2 else 0))) else (if x<3188 then (if x<2788 then (if x<2776 then 0 else 1) else (if x<3118 then 2 else 1)) else (if x<3276 then (if x<3256 then 2 else 1) else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers49 : Finset ℕ := ([1642,1678,1702,1746,1768,2618,2620,2638,2650,2652,2662,2674,2710,2730,2732,2762,2776,2788,2800,3118,3186,3188,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound49 : ListCliqueBound independentCachedEdge independentCachedBranchMembers49 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers49 2650 5
  · have he : independentCachedBranchMembers49.erase 2650=independentCachedBranchMembers47 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound47
  · have he : independentCachedBranchMembers49.filter (independentCachedEdge 2650)=independentCachedBranchMembers48 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound48
def independentCachedBranchMembers50 : Finset ℕ := ([1594,1628,1642,1652,1678,1686,1702,1720,1740,1746,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound50 : ListCliqueBound independentCachedEdge independentCachedBranchMembers50 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers50 1686 6
  · have he : independentCachedBranchMembers50.erase 1686=independentCachedBranchMembers44 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound44
  · have he : independentCachedBranchMembers50.filter (independentCachedEdge 1686)=independentCachedBranchMembers49 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound49
def independentCachedBranchMembers51 : Finset ℕ := ([1594,1628,1642,1702,1746,2614,2620,2650,2662,2668,2702,2710,2716,2730,2738,2758,2772,2792,2800,3118,3180,3188,3250,3256,3270,3276,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound51 : ListCliqueBound independentCachedEdge independentCachedBranchMembers51 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers51 6 (fun x => (if x<2738 then (if x<2650 then (if x<1702 then (if x<1628 then 0 else (if x<1642 then 0 else 1)) else (if x<2614 then (if x<1746 then 1 else 0) else (if x<2620 then 2 else 0))) else (if x<2702 then (if x<2662 then 0 else (if x<2668 then 1 else 2)) else (if x<2716 then (if x<2710 then 2 else 1) else (if x<2730 then 3 else 1)))) else (if x<3188 then (if x<2792 then (if x<2758 then 0 else (if x<2772 then 3 else 0)) else (if x<3118 then (if x<2800 then 3 else 4) else (if x<3180 then 2 else 5))) else (if x<3270 then (if x<3250 then 2 else (if x<3256 then 4 else 3)) else (if x<3284 then (if x<3276 then 5 else 2) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers52 : Finset ℕ := ([1594,1626,1628,1642,1652,1678,1686,1702,1720,1740,1746,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound52 : ListCliqueBound independentCachedEdge independentCachedBranchMembers52 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers52 1626 6
  · have he : independentCachedBranchMembers52.erase 1626=independentCachedBranchMembers50 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound50
  · have he : independentCachedBranchMembers52.filter (independentCachedEdge 1626)=independentCachedBranchMembers51 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound51
def independentCachedBranchMembers53 : Finset ℕ := ([1594,1628,1652,1720,1746,2620,2638,2650,2662,2674,2702,2710,2730,2738,2772,2776,2788,2792,3158,3178,3226,3238,3250,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound53 : ListCliqueBound independentCachedEdge independentCachedBranchMembers53 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers53 6 (fun x => (if x<2730 then (if x<2638 then (if x<1720 then (if x<1628 then 0 else (if x<1652 then 0 else 1)) else (if x<1746 then 1 else (if x<2620 then 0 else 0))) else (if x<2674 then (if x<2650 then 2 else (if x<2662 then 0 else 1)) else (if x<2702 then 2 else (if x<2710 then 3 else 2)))) else (if x<3158 then (if x<2776 then (if x<2738 then 1 else (if x<2772 then 0 else 0)) else (if x<2788 then 2 else (if x<2792 then 2 else 3))) else (if x<3238 then (if x<3178 then 1 else (if x<3226 then 4 else 1)) else (if x<3276 then (if x<3250 then 4 else 5) else (if x<3284 then 3 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers54 : Finset ℕ := ([1594,1652,2620,2638,2674,2702,2710,2730,2738,2776,2788,3226,3238,3276,3284] : List ℕ).toFinset
theorem independentCachedBranchBound54 : ListCliqueBound independentCachedEdge independentCachedBranchMembers54 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers54 5 (fun x => (if x<2730 then (if x<2638 then (if x<1652 then 0 else (if x<2620 then 0 else 0)) else (if x<2702 then (if x<2674 then 1 else 0) else (if x<2710 then 2 else 1))) else (if x<3226 then (if x<2776 then (if x<2738 then 0 else 2) else (if x<2788 then 1 else 0)) else (if x<3276 then (if x<3238 then 2 else 2) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers55 : Finset ℕ := ([1594,1628,1652,1720,1746,2620,2638,2650,2662,2674,2702,2710,2730,2738,2772,2776,2788,2792,3158,3178,3226,3238,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound55 : ListCliqueBound independentCachedEdge independentCachedBranchMembers55 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers55 3288 5
  · have he : independentCachedBranchMembers55.erase 3288=independentCachedBranchMembers53 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound53
  · have he : independentCachedBranchMembers55.filter (independentCachedEdge 3288)=independentCachedBranchMembers54 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound54
def independentCachedBranchMembers56 : Finset ℕ := ([1628,1720,2620,2638,2674,2710,2730,2772,2776,2788,2792,3158,3178,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound56 : ListCliqueBound independentCachedEdge independentCachedBranchMembers56 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers56 5 (fun x => (if x<2772 then (if x<2638 then (if x<1720 then 0 else (if x<2620 then 0 else 0)) else (if x<2710 then (if x<2674 then 0 else 1) else (if x<2730 then 1 else 0))) else (if x<3158 then (if x<2788 then (if x<2776 then 2 else 0) else (if x<2792 then 1 else 2)) else (if x<3250 then (if x<3178 then 2 else 2) else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers57 : Finset ℕ := ([1594,1628,1652,1720,1746,2620,2638,2650,2662,2674,2702,2710,2730,2738,2772,2776,2788,2792,3158,3178,3186,3226,3238,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound57 : ListCliqueBound independentCachedEdge independentCachedBranchMembers57 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers57 3186 5
  · have he : independentCachedBranchMembers57.erase 3186=independentCachedBranchMembers55 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound55
  · have he : independentCachedBranchMembers57.filter (independentCachedEdge 3186)=independentCachedBranchMembers56 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound56
def independentCachedBranchMembers58 : Finset ℕ := ([1594,1628,2638,2674,2702,2738,2772,2776,2788,2792,3158,3178,3226,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound58 : ListCliqueBound independentCachedEdge independentCachedBranchMembers58 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers58 5 (fun x => (if x<2776 then (if x<2674 then (if x<1628 then 0 else (if x<2638 then 0 else 1)) else (if x<2738 then (if x<2702 then 1 else 2) else (if x<2772 then 0 else 0))) else (if x<3178 then (if x<2792 then (if x<2788 then 1 else 1) else (if x<3158 then 2 else 3)) else (if x<3238 then (if x<3226 then 3 else 3) else (if x<3276 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers59 : Finset ℕ := ([1594,1628,1652,1720,1746,2620,2638,2650,2662,2674,2702,2710,2730,2738,2772,2776,2788,2792,2800,3158,3178,3186,3226,3238,3250,3276,3284,3288] : List ℕ).toFinset
theorem independentCachedBranchBound59 : ListCliqueBound independentCachedEdge independentCachedBranchMembers59 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers59 2800 5
  · have he : independentCachedBranchMembers59.erase 2800=independentCachedBranchMembers57 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound57
  · have he : independentCachedBranchMembers59.filter (independentCachedEdge 2800)=independentCachedBranchMembers58 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound58
def independentCachedBranchMembers60 : Finset ℕ := ([1594,1596,1626,1628,1642,1652,1678,1686,1702,1720,1740,1746,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound60 : ListCliqueBound independentCachedEdge independentCachedBranchMembers60 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers60 1596 6
  · have he : independentCachedBranchMembers60.erase 1596=independentCachedBranchMembers52 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound52
  · have he : independentCachedBranchMembers60.filter (independentCachedEdge 1596)=independentCachedBranchMembers59 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound59
def independentCachedBranchMembers61 : Finset ℕ := ([1594,1628,1678,1740,1746,1768,2614,2620,2638,2650,2710,2716,2732,2738,2762,2772,2788,2800,3102,3118,3158,3180,3186,3192,3226,3252,3270,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound61 : ListCliqueBound independentCachedEdge independentCachedBranchMembers61 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers61 6 (fun x => (if x<2772 then (if x<2620 then (if x<1740 then (if x<1628 then 0 else (if x<1678 then 0 else 0)) else (if x<1768 then (if x<1746 then 1 else 0) else (if x<2614 then 0 else 1))) else (if x<2716 then (if x<2650 then (if x<2638 then 2 else 1) else (if x<2710 then 2 else 2)) else (if x<2738 then (if x<2732 then 1 else 3) else (if x<2762 then 3 else 3)))) else (if x<3186 then (if x<3102 then (if x<2788 then 3 else (if x<2800 then 1 else 2)) else (if x<3158 then (if x<3118 then 2 else 4) else (if x<3180 then 4 else 5))) else (if x<3270 then (if x<3226 then (if x<3192 then 5 else 2) else (if x<3252 then 4 else 2)) else (if x<3288 then (if x<3276 then 5 else 3) else (if x<3298 then 5 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers62 : Finset ℕ := ([1594,1596,1626,1628,1642,1652,1678,1686,1702,1720,1740,1746,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound62 : ListCliqueBound independentCachedEdge independentCachedBranchMembers62 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers62 2740 6
  · have he : independentCachedBranchMembers62.erase 2740=independentCachedBranchMembers60 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound60
  · have he : independentCachedBranchMembers62.filter (independentCachedEdge 2740)=independentCachedBranchMembers61 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound61
def independentCachedBranchMembers63 : Finset ℕ := ([1594,1626,1652,1702,1740,1768,1776,2614,2620,2638,2652,2674,2680,2702,2710,2730,2762,2776,2788,3118,3158,3178,3186,3192,3250,3256,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound63 : ListCliqueBound independentCachedEdge independentCachedBranchMembers63 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers63 6 (fun x => (if x<2710 then (if x<2614 then (if x<1702 then (if x<1626 then 0 else (if x<1652 then 1 else 0)) else (if x<1768 then (if x<1740 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<2652 then (if x<2620 then 0 else (if x<2638 then 2 else 1)) else (if x<2680 then (if x<2674 then 3 else 1) else (if x<2702 then 0 else 2)))) else (if x<3178 then (if x<2776 then (if x<2730 then 3 else (if x<2762 then 0 else 3)) else (if x<3118 then (if x<2788 then 1 else 0) else (if x<3158 then 2 else 4))) else (if x<3250 then (if x<3186 then 4 else (if x<3192 then 5 else 2)) else (if x<3274 then (if x<3256 then 4 else 5) else (if x<3288 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers64 : Finset ℕ := ([1626,1652,1768,2614,2638,2652,2674,2710,2730,3118,3158,3178,3192,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound64 : ListCliqueBound independentCachedEdge independentCachedBranchMembers64 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers64 5 (fun x => (if x<2730 then (if x<2638 then (if x<1768 then (if x<1652 then 0 else 0) else (if x<2614 then 0 else 1)) else (if x<2674 then (if x<2652 then 1 else 2) else (if x<2710 then 2 else 2))) else (if x<3192 then (if x<3158 then (if x<3118 then 1 else 1) else (if x<3178 then 0 else 3)) else (if x<3274 then (if x<3250 then 0 else 1) else (if x<3288 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers65 : Finset ℕ := ([1594,1626,1652,1702,1740,1768,1776,2614,2620,2638,2652,2674,2680,2702,2710,2730,2738,2762,2776,2788,3118,3158,3178,3186,3192,3250,3256,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound65 : ListCliqueBound independentCachedEdge independentCachedBranchMembers65 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers65 2738 5
  · have he : independentCachedBranchMembers65.erase 2738=independentCachedBranchMembers63 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound63
  · have he : independentCachedBranchMembers65.filter (independentCachedEdge 2738)=independentCachedBranchMembers64 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound64
def independentCachedBranchMembers66 : Finset ℕ := ([1594,1626,1652,1702,1768,1776,2620,2652,2674,2702,2710,2776,3118,3158,3192,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound66 : ListCliqueBound independentCachedEdge independentCachedBranchMembers66 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers66 5 (fun x => (if x<2674 then (if x<1768 then (if x<1652 then (if x<1626 then 0 else 1) else (if x<1702 then 0 else 0)) else (if x<2620 then (if x<1776 then 0 else 1) else (if x<2652 then 2 else 3))) else (if x<3118 then (if x<2710 then (if x<2702 then 1 else 2) else (if x<2776 then 3 else 1)) else (if x<3192 then (if x<3158 then 2 else 3) else (if x<3250 then 0 else (if x<3274 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers67 : Finset ℕ := ([1594,1626,1652,1702,1740,1768,1776,2614,2620,2638,2652,2674,2680,2702,2710,2716,2730,2738,2762,2776,2788,3118,3158,3178,3186,3192,3250,3256,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound67 : ListCliqueBound independentCachedEdge independentCachedBranchMembers67 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers67 2716 5
  · have he : independentCachedBranchMembers67.erase 2716=independentCachedBranchMembers65 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound65
  · have he : independentCachedBranchMembers67.filter (independentCachedEdge 2716)=independentCachedBranchMembers66 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound66
def independentCachedBranchMembers68 : Finset ℕ := ([1594,1596,1626,1628,1642,1652,1678,1686,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound68 : ListCliqueBound independentCachedEdge independentCachedBranchMembers68 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers68 1764 6
  · have he : independentCachedBranchMembers68.erase 1764=independentCachedBranchMembers62 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound62
  · have he : independentCachedBranchMembers68.filter (independentCachedEdge 1764)=independentCachedBranchMembers67 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound67
def independentCachedBranchMembers69 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2758,2792,2800,3118,3158,3192,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound69 : ListCliqueBound independentCachedEdge independentCachedBranchMembers69 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers69 6 (fun x => (if x<2668 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1678 then 0 else (if x<1686 then 0 else 1))) else (if x<2618 then (if x<1740 then 1 else (if x<2614 then 2 else 2)) else (if x<2638 then 3 else (if x<2650 then 2 else 4)))) else (if x<2800 then (if x<2730 then (if x<2680 then 3 else (if x<2716 then 0 else 0)) else (if x<2758 then 4 else (if x<2792 then 4 else 5))) else (if x<3192 then (if x<3118 then 3 else (if x<3158 then 3 else 1)) else (if x<3250 then 1 else (if x<3274 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers70 : Finset ℕ := ([1628,1642,2614,2650,2668,2716,2730,2758,2792,2800,3158,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound70 : ListCliqueBound independentCachedEdge independentCachedBranchMembers70 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers70 5 (fun x => (if x<2730 then (if x<2650 then (if x<1642 then 0 else (if x<2614 then 0 else 1)) else (if x<2668 then 0 else (if x<2716 then 0 else 0))) else (if x<2800 then (if x<2758 then 0 else (if x<2792 then 1 else 2)) else (if x<3192 then (if x<3158 then 1 else 2) else (if x<3274 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers71 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2758,2792,2800,3118,3158,3192,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound71 : ListCliqueBound independentCachedEdge independentCachedBranchMembers71 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers71 3270 5
  · have he : independentCachedBranchMembers71.erase 3270=independentCachedBranchMembers69 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound69
  · have he : independentCachedBranchMembers71.filter (independentCachedEdge 3270)=independentCachedBranchMembers70 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound70
def independentCachedBranchMembers72 : Finset ℕ := ([1642,1686,1720,1740,2618,2638,2650,2716,2758,2792,3158,3192,3274] : List ℕ).toFinset
theorem independentCachedBranchBound72 : ListCliqueBound independentCachedEdge independentCachedBranchMembers72 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers72 5 (fun x => (if x<2650 then (if x<1740 then (if x<1686 then 0 else (if x<1720 then 1 else 0)) else (if x<2618 then 0 else (if x<2638 then 0 else 0))) else (if x<2792 then (if x<2716 then 2 else (if x<2758 then 0 else 1)) else (if x<3192 then (if x<3158 then 0 else 1) else (if x<3274 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers73 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2758,2792,2800,3118,3158,3188,3192,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound73 : ListCliqueBound independentCachedEdge independentCachedBranchMembers73 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers73 3188 5
  · have he : independentCachedBranchMembers73.erase 3188=independentCachedBranchMembers71 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound71
  · have he : independentCachedBranchMembers73.filter (independentCachedEdge 3188)=independentCachedBranchMembers72 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound72
def independentCachedBranchMembers74 : Finset ℕ := ([1596,1642,1720,1740,2618,2638,2668,2716,2792,2800,3118,3192,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound74 : ListCliqueBound independentCachedEdge independentCachedBranchMembers74 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers74 5 (fun x => (if x<2716 then (if x<1740 then (if x<1642 then 0 else (if x<1720 then 0 else 1)) else (if x<2638 then (if x<2618 then 0 else 0) else (if x<2668 then 1 else 0))) else (if x<3118 then (if x<2792 then 0 else (if x<2800 then 1 else 2)) else (if x<3250 then (if x<3192 then 2 else 2) else (if x<3270 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers75 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2758,2792,2800,3118,3158,3188,3192,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound75 : ListCliqueBound independentCachedEdge independentCachedBranchMembers75 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers75 3238 5
  · have he : independentCachedBranchMembers75.erase 3238=independentCachedBranchMembers73 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound73
  · have he : independentCachedBranchMembers75.filter (independentCachedEdge 3238)=independentCachedBranchMembers74 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound74
def independentCachedBranchMembers76 : Finset ℕ := ([1678,1720,2614,2618,2650,2668,2716,2730,2758,2800,3118,3188,3192,3250] : List ℕ).toFinset
theorem independentCachedBranchBound76 : ListCliqueBound independentCachedEdge independentCachedBranchMembers76 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers76 5 (fun x => (if x<2730 then (if x<2618 then (if x<1720 then 0 else (if x<2614 then 0 else 1)) else (if x<2668 then (if x<2650 then 2 else 1) else (if x<2716 then 1 else 0))) else (if x<3118 then (if x<2758 then 0 else (if x<2800 then 0 else 0)) else (if x<3192 then (if x<3188 then 2 else 3) else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers77 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2758,2792,2800,3118,3158,3180,3188,3192,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound77 : ListCliqueBound independentCachedEdge independentCachedBranchMembers77 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers77 3180 5
  · have he : independentCachedBranchMembers77.erase 3180=independentCachedBranchMembers75 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound75
  · have he : independentCachedBranchMembers77.filter (independentCachedEdge 3180)=independentCachedBranchMembers76 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound76
def independentCachedBranchMembers78 : Finset ℕ := ([1628,1686,1720,2614,2638,2650,2730,2758,2792,3118,3158,3180,3192,3238,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound78 : ListCliqueBound independentCachedEdge independentCachedBranchMembers78 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers78 5 (fun x => (if x<2792 then (if x<2638 then (if x<1720 then (if x<1686 then 0 else 0) else (if x<2614 then 0 else 1)) else (if x<2730 then (if x<2650 then 1 else 2) else (if x<2758 then 1 else 2))) else (if x<3192 then (if x<3158 then (if x<3118 then 2 else 1) else (if x<3180 then 0 else 3)) else (if x<3250 then (if x<3238 then 0 else 3) else (if x<3274 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers79 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2758,2762,2792,2800,3118,3158,3180,3188,3192,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound79 : ListCliqueBound independentCachedEdge independentCachedBranchMembers79 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers79 2762 5
  · have he : independentCachedBranchMembers79.erase 2762=independentCachedBranchMembers77 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound77
  · have he : independentCachedBranchMembers79.filter (independentCachedEdge 2762)=independentCachedBranchMembers78 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound78
def independentCachedBranchMembers80 : Finset ℕ := ([1596,1642,1678,2614,2618,2638,2668,2730,2800,3118,3158,3188,3192,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound80 : ListCliqueBound independentCachedEdge independentCachedBranchMembers80 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers80 5 (fun x => (if x<2800 then (if x<2618 then (if x<1678 then (if x<1642 then 0 else 0) else (if x<2614 then 0 else 1)) else (if x<2668 then (if x<2638 then 2 else 1) else (if x<2730 then 2 else 1))) else (if x<3192 then (if x<3158 then (if x<3118 then 2 else 0) else (if x<3188 then 1 else 3)) else (if x<3270 then (if x<3250 then 0 else 1) else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers81 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2738,2758,2762,2792,2800,3118,3158,3180,3188,3192,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound81 : ListCliqueBound independentCachedEdge independentCachedBranchMembers81 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers81 2738 5
  · have he : independentCachedBranchMembers81.erase 2738=independentCachedBranchMembers79 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound79
  · have he : independentCachedBranchMembers81.filter (independentCachedEdge 2738)=independentCachedBranchMembers80 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound80
def independentCachedBranchMembers82 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,2618,2650,2668,2758,2792,2800,3118,3158,3192,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound82 : ListCliqueBound independentCachedEdge independentCachedBranchMembers82 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers82 5 (fun x => (if x<2668 then (if x<1686 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1678 then 0 else 0)) else (if x<2618 then (if x<1720 then 1 else 1) else (if x<2650 then 2 else 3))) else (if x<3118 then (if x<2792 then (if x<2758 then 2 else 3) else (if x<2800 then 3 else 2)) else (if x<3192 then (if x<3158 then 0 else 1) else (if x<3250 then 0 else (if x<3274 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers83 : Finset ℕ := ([1596,1628,1642,1678,1686,1720,1740,2614,2618,2638,2650,2668,2680,2716,2730,2738,2758,2762,2788,2792,2800,3118,3158,3180,3188,3192,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound83 : ListCliqueBound independentCachedEdge independentCachedBranchMembers83 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers83 2788 5
  · have he : independentCachedBranchMembers83.erase 2788=independentCachedBranchMembers81 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound81
  · have he : independentCachedBranchMembers83.filter (independentCachedEdge 2788)=independentCachedBranchMembers82 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound82
def independentCachedBranchMembers84 : Finset ℕ := ([1594,1596,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound84 : ListCliqueBound independentCachedEdge independentCachedBranchMembers84 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers84 1692 6
  · have he : independentCachedBranchMembers84.erase 1692=independentCachedBranchMembers68 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound68
  · have he : independentCachedBranchMembers84.filter (independentCachedEdge 1692)=independentCachedBranchMembers83 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound83
def independentCachedBranchMembers85 : Finset ℕ := ([1626,1628,1642,1678,1720,1740,1776,2618,2620,2638,2674,2680,2710,2716,2730,2776,2788,2792,3186,3188,3192,3226,3238,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound85 : ListCliqueBound independentCachedEdge independentCachedBranchMembers85 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers85 6 (fun x => (if x<2716 then (if x<1776 then (if x<1678 then (if x<1628 then 0 else (if x<1642 then 1 else 1)) else (if x<1720 then 0 else (if x<1740 then 0 else 2))) else (if x<2638 then (if x<2618 then 1 else (if x<2620 then 2 else 3)) else (if x<2680 then (if x<2674 then 0 else 3) else (if x<2710 then 0 else 3)))) else (if x<3192 then (if x<2788 then (if x<2730 then 2 else (if x<2776 then 3 else 3)) else (if x<3186 then (if x<2792 then 3 else 2) else (if x<3188 then 4 else 5))) else (if x<3244 then (if x<3226 then 1 else (if x<3238 then 4 else 4)) else (if x<3288 then (if x<3284 then 5 else 1) else (if x<3298 then 5 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers86 : Finset ℕ := ([1626,1678,1720,2618,2710,2716,2730,2776,2788,3186,3192,3226,3238,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound86 : ListCliqueBound independentCachedEdge independentCachedBranchMembers86 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers86 5 (fun x => (if x<2788 then (if x<2710 then (if x<1720 then (if x<1678 then 0 else 0) else (if x<2618 then 0 else 1)) else (if x<2730 then (if x<2716 then 1 else 2) else (if x<2776 then 2 else 1))) else (if x<3238 then (if x<3192 then (if x<3186 then 2 else 3) else (if x<3226 then 0 else 0)) else (if x<3284 then (if x<3244 then 3 else 0) else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers87 : Finset ℕ := ([1626,1628,1642,1678,1720,1740,1776,2618,2620,2638,2674,2680,2710,2716,2730,2772,2776,2788,2792,3186,3188,3192,3226,3238,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound87 : ListCliqueBound independentCachedEdge independentCachedBranchMembers87 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers87 2772 5
  · have he : independentCachedBranchMembers87.erase 2772=independentCachedBranchMembers85 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound85
  · have he : independentCachedBranchMembers87.filter (independentCachedEdge 2772)=independentCachedBranchMembers86 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound86
def independentCachedBranchMembers88 : Finset ℕ := ([1628,1642,1776,2620,2674,2716,2730,2788,2792,3188,3192,3226,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound88 : ListCliqueBound independentCachedEdge independentCachedBranchMembers88 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers88 5 (fun x => (if x<2792 then (if x<2674 then (if x<1776 then (if x<1642 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<2730 then (if x<2716 then 1 else 2) else (if x<2788 then 1 else 1))) else (if x<3244 then (if x<3192 then (if x<3188 then 2 else 1) else (if x<3226 then 0 else 3)) else (if x<3288 then (if x<3284 then 1 else 0) else (if x<3298 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers89 : Finset ℕ := ([1626,1628,1642,1678,1720,1740,1776,2618,2620,2638,2674,2680,2710,2716,2730,2732,2772,2776,2788,2792,3186,3188,3192,3226,3238,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound89 : ListCliqueBound independentCachedEdge independentCachedBranchMembers89 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers89 2732 5
  · have he : independentCachedBranchMembers89.erase 2732=independentCachedBranchMembers87 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound87
  · have he : independentCachedBranchMembers89.filter (independentCachedEdge 2732)=independentCachedBranchMembers88 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound88
def independentCachedBranchMembers90 : Finset ℕ := ([1626,1628,1642,1678,1720,1776,2618,2620,2674,2710,2776,2792,3192,3226,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound90 : ListCliqueBound independentCachedEdge independentCachedBranchMembers90 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers90 5 (fun x => (if x<2674 then (if x<1720 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1678 then 1 else 0)) else (if x<2618 then (if x<1776 then 0 else 1) else (if x<2620 then 2 else 3))) else (if x<3192 then (if x<2776 then (if x<2710 then 3 else 2) else (if x<2792 then 2 else 3)) else (if x<3244 then (if x<3226 then 0 else 0) else (if x<3284 then 0 else (if x<3298 then 1 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers91 : Finset ℕ := ([1626,1628,1642,1678,1720,1740,1776,2614,2618,2620,2638,2674,2680,2710,2716,2730,2732,2772,2776,2788,2792,3186,3188,3192,3226,3238,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound91 : ListCliqueBound independentCachedEdge independentCachedBranchMembers91 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers91 2614 5
  · have he : independentCachedBranchMembers91.erase 2614=independentCachedBranchMembers89 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound89
  · have he : independentCachedBranchMembers91.filter (independentCachedEdge 2614)=independentCachedBranchMembers90 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound90
def independentCachedBranchMembers92 : Finset ℕ := ([1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound92 : ListCliqueBound independentCachedEdge independentCachedBranchMembers92 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers92 1614 6
  · have he : independentCachedBranchMembers92.erase 1614=independentCachedBranchMembers84 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound84
  · have he : independentCachedBranchMembers92.filter (independentCachedEdge 1614)=independentCachedBranchMembers91 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound91
def independentCachedBranchMembers93 : Finset ℕ := ([1594,1596,1652,1686,1702,1740,1768,2614,2650,2652,2668,2680,2702,2716,2730,2758,2788,2800,3180,3192,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound93 : ListCliqueBound independentCachedEdge independentCachedBranchMembers93 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers93 6 (fun x => (if x<2702 then (if x<1768 then (if x<1686 then (if x<1596 then 0 else (if x<1652 then 1 else 0)) else (if x<1702 then 0 else (if x<1740 then 1 else 1))) else (if x<2652 then (if x<2614 then 2 else (if x<2650 then 0 else 3)) else (if x<2668 then 1 else (if x<2680 then 2 else 0)))) else (if x<3180 then (if x<2758 then (if x<2716 then 3 else (if x<2730 then 4 else 2)) else (if x<2788 then 1 else (if x<2800 then 4 else 2))) else (if x<3244 then (if x<3192 then 5 else (if x<3226 then 3 else 3)) else (if x<3284 then (if x<3270 then 3 else 5) else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers94 : Finset ℕ := ([1652,1686,1702,1740,2614,2650,2652,2668,2702,2788,3192,3226,3244,3270] : List ℕ).toFinset
theorem independentCachedBranchBound94 : ListCliqueBound independentCachedEdge independentCachedBranchMembers94 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers94 5 (fun x => (if x<2668 then (if x<1740 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<2650 then (if x<2614 then 0 else 0) else (if x<2652 then 1 else 2))) else (if x<3192 then (if x<2702 then 0 else (if x<2788 then 0 else 2)) else (if x<3244 then (if x<3226 then 1 else 3) else (if x<3270 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers95 : Finset ℕ := ([1594,1596,1652,1686,1702,1740,1768,2614,2650,2652,2668,2680,2702,2716,2730,2758,2788,2800,3180,3192,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound95 : ListCliqueBound independentCachedEdge independentCachedBranchMembers95 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers95 3256 5
  · have he : independentCachedBranchMembers95.erase 3256=independentCachedBranchMembers93 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound93
  · have he : independentCachedBranchMembers95.filter (independentCachedEdge 3256)=independentCachedBranchMembers94 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound94
def independentCachedBranchMembers96 : Finset ℕ := ([1596,1652,1702,1740,2614,2652,2702,2758,2788,2800,3180,3192,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound96 : ListCliqueBound independentCachedEdge independentCachedBranchMembers96 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers96 5 (fun x => (if x<2758 then (if x<1740 then (if x<1652 then 0 else (if x<1702 then 1 else 0)) else (if x<2652 then (if x<2614 then 0 else 0) else (if x<2702 then 0 else 1))) else (if x<3180 then (if x<2788 then 0 else (if x<2800 then 1 else 2)) else (if x<3284 then (if x<3192 then 3 else 2) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers97 : Finset ℕ := ([1594,1596,1652,1686,1702,1740,1768,2614,2650,2652,2668,2680,2702,2716,2730,2758,2788,2800,3178,3180,3192,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound97 : ListCliqueBound independentCachedEdge independentCachedBranchMembers97 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers97 3178 5
  · have he : independentCachedBranchMembers97.erase 3178=independentCachedBranchMembers95 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound95
  · have he : independentCachedBranchMembers97.filter (independentCachedEdge 3178)=independentCachedBranchMembers96 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound96
def independentCachedBranchMembers98 : Finset ℕ := ([1596,1702,1768,2652,2716,2730,2758,2788,2800,3180,3192,3226,3244,3256,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound98 : ListCliqueBound independentCachedEdge independentCachedBranchMembers98 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers98 5 (fun x => (if x<2800 then (if x<2716 then (if x<1768 then (if x<1702 then 0 else 0) else (if x<2652 then 0 else 1)) else (if x<2758 then (if x<2730 then 2 else 2) else (if x<2788 then 1 else 2))) else (if x<3244 then (if x<3192 then (if x<3180 then 1 else 3) else (if x<3226 then 0 else 2)) else (if x<3284 then (if x<3256 then 0 else 3) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers99 : Finset ℕ := ([1594,1596,1652,1686,1702,1740,1768,2614,2650,2652,2668,2680,2702,2716,2730,2758,2772,2788,2800,3178,3180,3192,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound99 : ListCliqueBound independentCachedEdge independentCachedBranchMembers99 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers99 2772 5
  · have he : independentCachedBranchMembers99.erase 2772=independentCachedBranchMembers97 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound97
  · have he : independentCachedBranchMembers99.filter (independentCachedEdge 2772)=independentCachedBranchMembers98 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound98
def independentCachedBranchMembers100 : Finset ℕ := ([1594,1652,1686,2650,2668,2702,2716,2730,2788,3178,3192,3226,3244,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers100 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers100 5 (fun x => (if x<2788 then (if x<2668 then (if x<1686 then (if x<1652 then 0 else 0) else (if x<2650 then 0 else 1)) else (if x<2716 then (if x<2702 then 1 else 1) else (if x<2730 then 2 else 2))) else (if x<3244 then (if x<3192 then (if x<3178 then 2 else 3) else (if x<3226 then 0 else 0)) else (if x<3284 then (if x<3270 then 1 else 3) else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers101 : Finset ℕ := ([1594,1596,1652,1686,1702,1740,1768,2614,2650,2652,2668,2680,2702,2716,2730,2732,2758,2772,2788,2800,3178,3180,3192,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers101 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers101 2732 5
  · have he : independentCachedBranchMembers101.erase 2732=independentCachedBranchMembers99 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound99
  · have he : independentCachedBranchMembers101.filter (independentCachedEdge 2732)=independentCachedBranchMembers100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound100
def independentCachedBranchMembers102 : Finset ℕ := ([1594,1596,1652,1686,1702,1768,2650,2652,2668,2702,2758,2800,3192,3226,3244,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers102 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers102 5 (fun x => (if x<2668 then (if x<1702 then (if x<1652 then (if x<1596 then 0 else 1) else (if x<1686 then 0 else 0)) else (if x<2650 then (if x<1768 then 1 else 1) else (if x<2652 then 2 else 3))) else (if x<3192 then (if x<2758 then (if x<2702 then 2 else 2) else (if x<2800 then 3 else 3)) else (if x<3244 then (if x<3226 then 0 else 0) else (if x<3284 then 1 else (if x<3298 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers103 : Finset ℕ := ([1594,1596,1652,1686,1702,1740,1768,2614,2638,2650,2652,2668,2680,2702,2716,2730,2732,2758,2772,2788,2800,3178,3180,3192,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers103 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers103 2638 5
  · have he : independentCachedBranchMembers103.erase 2638=independentCachedBranchMembers101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound101
  · have he : independentCachedBranchMembers103.filter (independentCachedEdge 2638)=independentCachedBranchMembers102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound102
def independentCachedBranchMembers104 : Finset ℕ := ([1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers104 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers104 1590 6
  · have he : independentCachedBranchMembers104.erase 1590=independentCachedBranchMembers92 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound92
  · have he : independentCachedBranchMembers104.filter (independentCachedEdge 1590)=independentCachedBranchMembers103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound103
def independentCachedBranchMembers105 : Finset ℕ := ([1590,1594,1614,1626,1642,1678,1686,1702,1746,2614,2618,2638,2650,2662,2674,2702,2710,2730,2738,2758,2762,3102,3118,3158,3178,3186,3226,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers105 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers105 6 (fun x => (if x<2702 then (if x<1702 then (if x<1626 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1678 then (if x<1642 then 2 else 3) else (if x<1686 then 1 else 2))) else (if x<2638 then (if x<2614 then (if x<1746 then 3 else 0) else (if x<2618 then 4 else 5)) else (if x<2662 then (if x<2650 then 4 else 3) else (if x<2674 then 3 else 1)))) else (if x<3158 then (if x<2758 then (if x<2730 then (if x<2710 then 5 else 3) else (if x<2738 then 1 else 0)) else (if x<3102 then (if x<2762 then 1 else 0) else (if x<3118 then 2 else 4))) else (if x<3238 then (if x<3186 then (if x<3178 then 4 else 2) else (if x<3226 then 5 else 5)) else (if x<3270 then (if x<3250 then 2 else 4) else (if x<3274 then 5 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers106 : Finset ℕ := ([1594,1614,1626,1678,1686,2614,2618,2638,2650,2702,2710,3102,3178,3186,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers106 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers106 5 (fun x => (if x<2702 then (if x<1686 then (if x<1626 then (if x<1614 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2618 then (if x<2614 then 0 else 2) else (if x<2638 then 3 else (if x<2650 then 1 else 2)))) else (if x<3186 then (if x<3102 then (if x<2710 then 2 else 3) else (if x<3178 then 0 else 0)) else (if x<3250 then (if x<3238 then 2 else 2) else (if x<3270 then 0 else (if x<3274 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers107 : Finset ℕ := ([1594,1686,2614,2638,2650,2702,3178,3270] : List ℕ).toFinset
theorem independentCachedBranchBound107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers107 4 (fun x => (if x<2650 then (if x<2614 then (if x<1686 then 0 else 0) else (if x<2638 then 0 else 1)) else (if x<3178 then (if x<2702 then 2 else 2) else (if x<3270 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers108 : Finset ℕ := ([1590,1594,1614,1626,1678,1686,2614,2618,2638,2650,2702,2710,3102,3178,3186,3238,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers108 1590 4
  · have he : independentCachedBranchMembers108.erase 1590=independentCachedBranchMembers106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound106
  · have he : independentCachedBranchMembers108.filter (independentCachedEdge 1590)=independentCachedBranchMembers107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound107
def independentCachedBranchMembers109 : Finset ℕ := ([1590,1594,1614,1626,1642,1678,1686,1702,1746,2614,2618,2638,2650,2662,2674,2702,2710,2730,2738,2758,2762,3102,3118,3158,3178,3186,3226,3238,3250,3270,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers109 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers109 3298 5
  · have he : independentCachedBranchMembers109.erase 3298=independentCachedBranchMembers105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound105
  · have he : independentCachedBranchMembers109.filter (independentCachedEdge 3298)=independentCachedBranchMembers108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound108
def independentCachedBranchMembers110 : Finset ℕ := ([252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers110 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers110 252 6
  · have he : independentCachedBranchMembers110.erase 252=independentCachedBranchMembers104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound104
  · have he : independentCachedBranchMembers110.filter (independentCachedEdge 252)=independentCachedBranchMembers109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound109
def independentCachedBranchMembers111 : Finset ℕ := ([1590,1614,1628,1652,1720,1746,1768,2614,2620,2638,2652,2662,2668,2730,2738,2762,2776,2792,2800,3102,3118,3158,3180,3188,3250,3256,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers111 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers111 6 (fun x => (if x<2738 then (if x<2614 then (if x<1652 then (if x<1614 then 0 else (if x<1628 then 0 else 1)) else (if x<1746 then (if x<1720 then 2 else 1) else (if x<1768 then 0 else 2))) else (if x<2652 then (if x<2620 then 2 else (if x<2638 then 1 else 1)) else (if x<2668 then (if x<2662 then 3 else 3) else (if x<2730 then 2 else 1)))) else (if x<3158 then (if x<2792 then (if x<2762 then 0 else (if x<2776 then 0 else 1)) else (if x<3102 then (if x<2800 then 3 else 2) else (if x<3118 then 4 else 5))) else (if x<3256 then (if x<3188 then (if x<3180 then 3 else 3) else (if x<3250 then 4 else 4)) else (if x<3288 then (if x<3274 then 5 else 5) else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers112 : Finset ℕ := ([1614,1652,1720,1746,1768,2614,2620,2652,2662,2668,2730,2762,2800,3158,3180,3274] : List ℕ).toFinset
theorem independentCachedBranchBound112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers112 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers112 5 (fun x => (if x<2662 then (if x<1768 then (if x<1720 then (if x<1652 then 0 else 0) else (if x<1746 then 1 else 0)) else (if x<2620 then (if x<2614 then 0 else 2) else (if x<2652 then 1 else 2))) else (if x<2800 then (if x<2730 then (if x<2668 then 1 else 0) else (if x<2762 then 1 else 0)) else (if x<3180 then (if x<3158 then 0 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers113 : Finset ℕ := ([1590,1614,1628,1652,1720,1746,1768,1776,2614,2620,2638,2652,2662,2668,2730,2738,2762,2776,2792,2800,3102,3118,3158,3180,3188,3250,3256,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers113 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers113 1776 5
  · have he : independentCachedBranchMembers113.erase 1776=independentCachedBranchMembers111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound111
  · have he : independentCachedBranchMembers113.filter (independentCachedEdge 1776)=independentCachedBranchMembers112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound112
def independentCachedBranchMembers114 : Finset ℕ := ([1590,1628,1652,1720,1746,2620,2638,2662,2730,2738,2776,2792,2800,3158,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers114 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers114 5 (fun x => (if x<2730 then (if x<1746 then (if x<1652 then (if x<1628 then 0 else 0) else (if x<1720 then 1 else 0)) else (if x<2638 then (if x<2620 then 0 else 0) else (if x<2662 then 2 else 1))) else (if x<2800 then (if x<2776 then (if x<2738 then 1 else 0) else (if x<2792 then 0 else 2)) else (if x<3250 then (if x<3158 then 1 else 2) else (if x<3288 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers115 : Finset ℕ := ([1590,1596,1614,1628,1652,1720,1746,1768,1776,2614,2620,2638,2652,2662,2668,2730,2738,2762,2776,2792,2800,3102,3118,3158,3180,3188,3250,3256,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers115 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers115 1596 5
  · have he : independentCachedBranchMembers115.erase 1596=independentCachedBranchMembers113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound113
  · have he : independentCachedBranchMembers115.filter (independentCachedEdge 1596)=independentCachedBranchMembers114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound114
def independentCachedBranchMembers116 : Finset ℕ := ([1590,1596,1614,1628,1768,1776,2614,2620,2638,2652,2792,2800,3102,3180,3188,3250,3256,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers116 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers116 5 (fun x => (if x<2652 then (if x<1768 then (if x<1614 then (if x<1596 then 0 else 1) else (if x<1628 then 0 else 2)) else (if x<2614 then (if x<1776 then 1 else 2) else (if x<2620 then 1 else (if x<2638 then 3 else 2)))) else (if x<3188 then (if x<2800 then (if x<2792 then 4 else 3) else (if x<3102 then 4 else (if x<3180 then 0 else 3))) else (if x<3256 then (if x<3250 then 4 else 0) else (if x<3274 then 3 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers117 : Finset ℕ := ([1590,1596,1614,1628,1652,1720,1746,1768,1776,2614,2620,2638,2652,2662,2668,2730,2738,2762,2776,2792,2800,3102,3118,3158,3180,3188,3226,3250,3256,3274,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers117 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers117 3226 5
  · have he : independentCachedBranchMembers117.erase 3226=independentCachedBranchMembers115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound115
  · have he : independentCachedBranchMembers117.filter (independentCachedEdge 3226)=independentCachedBranchMembers116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound116
def independentCachedBranchMembers118 : Finset ℕ := ([132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers118 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers118 132 6
  · have he : independentCachedBranchMembers118.erase 132=independentCachedBranchMembers110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound110
  · have he : independentCachedBranchMembers118.filter (independentCachedEdge 132)=independentCachedBranchMembers117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound117
def independentCachedBranchMembers119 : Finset ℕ := ([1594,1652,1678,1692,1720,1746,1764,1776,2618,2620,2662,2674,2702,2716,2730,2732,2758,2772,2788,2800,3102,3118,3186,3188,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers119 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers119 6 (fun x => (if x<2732 then (if x<1776 then (if x<1692 then (if x<1652 then 0 else (if x<1678 then 0 else 1)) else (if x<1746 then (if x<1720 then 0 else 1) else (if x<1764 then 0 else 1))) else (if x<2674 then (if x<2620 then (if x<2618 then 2 else 3) else (if x<2662 then 0 else 3)) else (if x<2716 then (if x<2702 then 0 else 2) else (if x<2730 then 4 else 4)))) else (if x<3186 then (if x<2788 then (if x<2758 then 1 else (if x<2772 then 1 else 0)) else (if x<3102 then (if x<2800 then 2 else 1) else (if x<3118 then 2 else 3))) else (if x<3256 then (if x<3226 then (if x<3188 then 3 else 2) else (if x<3244 then 3 else 4)) else (if x<3284 then (if x<3270 then 5 else 3) else (if x<3298 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers120 : Finset ℕ := ([1594,1652,1692,1720,1746,2620,2662,2674,2702,2730,2772,2788,2800,3186,3226,3284] : List ℕ).toFinset
theorem independentCachedBranchBound120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers120 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers120 5 (fun x => (if x<2702 then (if x<1746 then (if x<1692 then (if x<1652 then 0 else 0) else (if x<1720 then 0 else 1)) else (if x<2662 then (if x<2620 then 0 else 0) else (if x<2674 then 1 else 0))) else (if x<2800 then (if x<2772 then (if x<2730 then 2 else 1) else (if x<2788 then 0 else 2)) else (if x<3226 then (if x<3186 then 1 else 3) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers121 : Finset ℕ := ([1594,1596,1652,1678,1692,1720,1746,1764,1776,2618,2620,2662,2674,2702,2716,2730,2732,2758,2772,2788,2800,3102,3118,3186,3188,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers121 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers121 1596 5
  · have he : independentCachedBranchMembers121.erase 1596=independentCachedBranchMembers119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound119
  · have he : independentCachedBranchMembers121.filter (independentCachedEdge 1596)=independentCachedBranchMembers120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound120
def independentCachedBranchMembers122 : Finset ℕ := ([1594,1596,1678,1692,1764,1776,2618,2620,2702,2716,2788,2800,3102,3186,3188,3244,3256,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers122 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers122 5 (fun x => (if x<2716 then (if x<1764 then (if x<1678 then (if x<1596 then 0 else 1) else (if x<1692 then 0 else 2)) else (if x<2618 then (if x<1776 then 1 else 2) else (if x<2620 then 1 else (if x<2702 then 3 else 2)))) else (if x<3188 then (if x<2800 then (if x<2788 then 4 else 3) else (if x<3102 then 4 else (if x<3186 then 0 else 0))) else (if x<3256 then (if x<3244 then 3 else 3) else (if x<3270 then 4 else (if x<3284 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers123 : Finset ℕ := ([1594,1596,1652,1678,1692,1720,1746,1764,1776,2618,2620,2662,2674,2702,2716,2730,2732,2758,2772,2788,2800,3102,3118,3158,3186,3188,3226,3244,3256,3270,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers123 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers123 3158 5
  · have he : independentCachedBranchMembers123.erase 3158=independentCachedBranchMembers121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound121
  · have he : independentCachedBranchMembers123.filter (independentCachedEdge 3158)=independentCachedBranchMembers122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound122
def independentCachedBranchMembers124 : Finset ℕ := ([72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers124 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers124 72 6
  · have he : independentCachedBranchMembers124.erase 72=independentCachedBranchMembers118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound118
  · have he : independentCachedBranchMembers124.filter (independentCachedEdge 72)=independentCachedBranchMembers123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound123
def independentCachedBranchMembers125 : Finset ℕ := ([1626,1628,1642,1686,1692,1702,1746,1764,1768,2650,2652,2662,2668,2710,2716,2730,2732,2772,2776,2788,2792,3102,3118,3158,3178,3180,3226,3238,3244,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers125 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers125 6 (fun x => (if x<2732 then (if x<1768 then (if x<1692 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1686 then 1 else 0)) else (if x<1746 then (if x<1702 then 2 else 2) else (if x<1764 then 1 else 1))) else (if x<2668 then (if x<2652 then (if x<2650 then 2 else 1) else (if x<2662 then 3 else 3)) else (if x<2716 then (if x<2710 then 1 else 2) else (if x<2730 then 4 else 4)))) else (if x<3178 then (if x<2792 then (if x<2776 then (if x<2772 then 2 else 1) else (if x<2788 then 2 else 4)) else (if x<3118 then (if x<3102 then 3 else 0) else (if x<3158 then 5 else 3))) else (if x<3244 then (if x<3226 then (if x<3180 then 0 else 3) else (if x<3238 then 4 else 0)) else (if x<3288 then (if x<3284 then 4 else 4) else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers126 : Finset ℕ := ([48,72,132,252,1590,1594,1596,1614,1626,1628,1642,1652,1678,1686,1692,1702,1720,1740,1746,1764,1768,1776,2614,2618,2620,2638,2650,2652,2662,2668,2674,2680,2702,2710,2716,2730,2732,2738,2740,2758,2762,2772,2776,2788,2792,2800,3102,3118,3158,3178,3180,3186,3188,3192,3226,3238,3244,3250,3252,3256,3270,3274,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers126 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers126 48 6
  · have he : independentCachedBranchMembers126.erase 48=independentCachedBranchMembers124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound124
  · have he : independentCachedBranchMembers126.filter (independentCachedEdge 48)=independentCachedBranchMembers125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound125
def independentCachedBranchMembers127 : Finset ℕ := ([1594,1596,1614,1626,1652,1692,1702,1746,1768,2620,2650,2652,2662,2674,2702,2738,2740,2758,2772,2792,3102,3158,3178,3180,3192,3244,3256,3274,3276,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers127 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers127 6 (fun x => (if x<2738 then (if x<1746 then (if x<1626 then (if x<1596 then 0 else (if x<1614 then 1 else 0)) else (if x<1692 then (if x<1652 then 1 else 0) else (if x<1702 then 0 else 0))) else (if x<2652 then (if x<2620 then (if x<1768 then 0 else 0) else (if x<2650 then 2 else 2)) else (if x<2674 then (if x<2662 then 1 else 2) else (if x<2702 then 3 else 2)))) else (if x<3180 then (if x<2792 then (if x<2758 then (if x<2740 then 2 else 1) else (if x<2772 then 3 else 2)) else (if x<3158 then (if x<3102 then 2 else 4) else (if x<3178 then 3 else 4))) else (if x<3274 then (if x<3244 then (if x<3192 then 5 else 3) else (if x<3256 then 4 else 5)) else (if x<3288 then (if x<3276 then 5 else 3) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
