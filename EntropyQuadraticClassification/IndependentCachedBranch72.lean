/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch71
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5088 : Finset ℕ := ([34,72,144,250,1594,1614,1642,1652,1686,1708,1714,1752,1762,2614,2652,2662,2680,2714,2762,2772,2800,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5088 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5088 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5088 34 4
  · have he : independentCachedBranchMembers5088.erase 34=independentCachedBranchMembers5086 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5086
  · have he : independentCachedBranchMembers5088.filter (independentCachedEdge 34)=independentCachedBranchMembers5087 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5087
def independentCachedBranchMembers5089 : Finset ℕ := ([34,72,144,250,1594,1614,1686,1762,2614,2652,2714,2800,3118,3162,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5089 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5089 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5089 4 (fun x => (if x<2614 then (if x<1594 then (if x<144 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1686 then (if x<1614 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2652 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3228 then (if x<3162 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5090 : Finset ℕ := ([34,72,144,250,1594,1614,1642,1652,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2714,2762,2772,2800,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5090 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5090 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5090 1734 4
  · have he : independentCachedBranchMembers5090.erase 1734=independentCachedBranchMembers5088 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5088
  · have he : independentCachedBranchMembers5090.filter (independentCachedEdge 1734)=independentCachedBranchMembers5089 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5089
def independentCachedBranchMembers5091 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5091 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5091 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5091 3244 5
  · have he : independentCachedBranchMembers5091.erase 3244=independentCachedBranchMembers5077 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5077
  · have he : independentCachedBranchMembers5091.filter (independentCachedEdge 3244)=independentCachedBranchMembers5090 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5090
def independentCachedBranchMembers5092 : Finset ℕ := ([1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5092 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5092 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5092 5 (fun x => (if x<2740 then (if x<2662 then (if x<1714 then (if x<1708 then 0 else 0) else (if x<1734 then 0 else (if x<1752 then 0 else 0))) else (if x<2674 then (if x<2668 then 1 else 2) else (if x<2680 then 2 else (if x<2730 then 1 else 1)))) else (if x<3150 then (if x<2772 then (if x<2762 then 1 else 2) else (if x<3118 then 2 else (if x<3130 then 3 else 4))) else (if x<3228 then (if x<3162 then 4 else (if x<3222 then 3 else 3)) else (if x<3298 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5093 : Finset ℕ := ([1708,1734,2662,2668,2740,2772,3118,3150,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound5093 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5093 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5093 4 (fun x => (if x<2772 then (if x<2662 then (if x<1734 then 0 else 0) else (if x<2668 then 1 else (if x<2740 then 2 else 1))) else (if x<3150 then (if x<3118 then 2 else 2) else (if x<3222 then 1 else (if x<3228 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5094 : Finset ℕ := ([250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5094 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5094 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5094 250 4
  · have he : independentCachedBranchMembers5094.erase 250=independentCachedBranchMembers5092 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5092
  · have he : independentCachedBranchMembers5094.filter (independentCachedEdge 250)=independentCachedBranchMembers5093 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5093
def independentCachedBranchMembers5095 : Finset ℕ := ([1708,1734,2674,2680,2730,2762,3130,3162,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5095 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5095 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5095 4 (fun x => (if x<2762 then (if x<2674 then (if x<1734 then 0 else 0) else (if x<2680 then 1 else (if x<2730 then 2 else 1))) else (if x<3162 then (if x<3130 then 2 else 1) else (if x<3298 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5096 : Finset ℕ := ([144,250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5096 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5096 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5096 144 4
  · have he : independentCachedBranchMembers5096.erase 144=independentCachedBranchMembers5094 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5094
  · have he : independentCachedBranchMembers5096.filter (independentCachedEdge 144)=independentCachedBranchMembers5095 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5095
def independentCachedBranchMembers5097 : Finset ℕ := ([1714,1752,2668,2680,2730,2772,3118,3130,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5097 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5097 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5097 4 (fun x => (if x<2772 then (if x<2668 then (if x<1752 then 0 else 0) else (if x<2680 then 1 else (if x<2730 then 2 else 1))) else (if x<3130 then (if x<3118 then 2 else 1) else (if x<3222 then 2 else (if x<3304 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5098 : Finset ℕ := ([66,144,250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5098 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5098 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5098 66 4
  · have he : independentCachedBranchMembers5098.erase 66=independentCachedBranchMembers5096 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5096
  · have he : independentCachedBranchMembers5098.filter (independentCachedEdge 66)=independentCachedBranchMembers5097 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5097
def independentCachedBranchMembers5099 : Finset ℕ := ([1714,1752,2662,2674,2740,2762,3150,3162,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5099 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5099 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5099 4 (fun x => (if x<2762 then (if x<2662 then (if x<1752 then 0 else 0) else (if x<2674 then 1 else (if x<2740 then 2 else 1))) else (if x<3162 then (if x<3150 then 2 else 1) else (if x<3228 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5100 : Finset ℕ := ([40,66,144,250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5100 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5100 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5100 40 4
  · have he : independentCachedBranchMembers5100.erase 40=independentCachedBranchMembers5098 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5098
  · have he : independentCachedBranchMembers5100.filter (independentCachedEdge 40)=independentCachedBranchMembers5099 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5099
def independentCachedBranchMembers5101 : Finset ℕ := ([144,250,1714,1752,2674,2680,2740,2772,3130,3162,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound5101 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5101 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5101 4 (fun x => (if x<2740 then (if x<1752 then (if x<250 then 0 else (if x<1714 then 0 else 0)) else (if x<2674 then 0 else (if x<2680 then 1 else 2))) else (if x<3162 then (if x<2772 then 1 else (if x<3130 then 2 else 2)) else (if x<3222 then 1 else (if x<3228 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5102 : Finset ℕ := ([40,66,144,238,250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5102 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5102 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5102 238 4
  · have he : independentCachedBranchMembers5102.erase 238=independentCachedBranchMembers5100 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5100
  · have he : independentCachedBranchMembers5102.filter (independentCachedEdge 238)=independentCachedBranchMembers5101 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5101
def independentCachedBranchMembers5103 : Finset ℕ := ([144,250,1714,1752,2662,2668,2730,2762,3118,3150,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5103 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5103 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5103 4 (fun x => (if x<2730 then (if x<1752 then (if x<250 then 0 else (if x<1714 then 0 else 0)) else (if x<2662 then 0 else (if x<2668 then 1 else 2))) else (if x<3150 then (if x<2762 then 1 else (if x<3118 then 2 else 1)) else (if x<3298 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5104 : Finset ℕ := ([40,66,132,144,238,250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5104 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5104 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5104 132 4
  · have he : independentCachedBranchMembers5104.erase 132=independentCachedBranchMembers5102 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5102
  · have he : independentCachedBranchMembers5104.filter (independentCachedEdge 132)=independentCachedBranchMembers5103 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5103
def independentCachedBranchMembers5105 : Finset ℕ := ([40,66,1708,1734,2662,2674,2730,2772,3118,3130,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5105 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5105 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5105 4 (fun x => (if x<2730 then (if x<1734 then (if x<66 then 0 else (if x<1708 then 0 else 0)) else (if x<2662 then 0 else (if x<2674 then 1 else 2))) else (if x<3130 then (if x<2772 then 1 else (if x<3118 then 2 else 1)) else (if x<3228 then 2 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5106 : Finset ℕ := ([40,66,72,132,144,238,250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5106 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5106 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5106 72 4
  · have he : independentCachedBranchMembers5106.erase 72=independentCachedBranchMembers5104 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5104
  · have he : independentCachedBranchMembers5106.filter (independentCachedEdge 72)=independentCachedBranchMembers5105 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5105
def independentCachedBranchMembers5107 : Finset ℕ := ([40,66,1708,1734,2668,2680,2740,2762,3150,3162,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5107 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5107 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5107 4 (fun x => (if x<2740 then (if x<1734 then (if x<66 then 0 else (if x<1708 then 0 else 0)) else (if x<2668 then 0 else (if x<2680 then 1 else 2))) else (if x<3162 then (if x<2762 then 1 else (if x<3150 then 2 else 1)) else (if x<3222 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5108 : Finset ℕ := ([34,40,66,72,132,144,238,250,1642,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5108 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5108 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5108 34 4
  · have he : independentCachedBranchMembers5108.erase 34=independentCachedBranchMembers5106 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5106
  · have he : independentCachedBranchMembers5108.filter (independentCachedEdge 34)=independentCachedBranchMembers5107 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5107
def independentCachedBranchMembers5109 : Finset ℕ := ([34,40,66,72,132,144,238,250,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5109 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5109 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5109 4 (fun x => (if x<3118 then (if x<132 then (if x<66 then (if x<40 then 0 else 1) else (if x<72 then 1 else 0)) else (if x<238 then (if x<144 then 0 else 1) else (if x<250 then 0 else 1))) else (if x<3222 then (if x<3150 then (if x<3130 then 2 else 3) else (if x<3162 then 3 else 2)) else (if x<3298 then (if x<3228 then 2 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5110 : Finset ℕ := ([34,40,66,72,132,144,238,250,1642,1652,1708,1714,1734,1752,2662,2668,2674,2680,2730,2740,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5110 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5110 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5110 1652 4
  · have he : independentCachedBranchMembers5110.erase 1652=independentCachedBranchMembers5108 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5108
  · have he : independentCachedBranchMembers5110.filter (independentCachedEdge 1652)=independentCachedBranchMembers5109 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5109
def independentCachedBranchMembers5111 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5111 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5111 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5111 3102 5
  · have he : independentCachedBranchMembers5111.erase 3102=independentCachedBranchMembers5091 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5091
  · have he : independentCachedBranchMembers5111.filter (independentCachedEdge 3102)=independentCachedBranchMembers5110 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5110
def independentCachedBranchMembers5112 : Finset ℕ := ([1652,1708,1714,1734,1752,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5112 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5112 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5112 5 (fun x => (if x<2668 then (if x<2614 then (if x<1714 then (if x<1708 then 0 else 0) else (if x<1734 then 0 else (if x<1752 then 0 else 0))) else (if x<2646 then (if x<2620 then 1 else 2) else (if x<2652 then 2 else (if x<2662 then 1 else 3)))) else (if x<2730 then (if x<2680 then (if x<2674 then 4 else 4) else (if x<2702 then 3 else (if x<2714 then 1 else 2))) else (if x<2772 then (if x<2740 then 3 else (if x<2762 then 3 else 4)) else (if x<2788 then 4 else (if x<2800 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5113 : Finset ℕ := ([1708,1752,2620,2652,2662,2674,2702,2714,2740,2772] : List ℕ).toFinset
theorem independentCachedBranchBound5113 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5113 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5113 4 (fun x => (if x<2674 then (if x<2620 then (if x<1752 then 0 else 0) else (if x<2652 then 1 else (if x<2662 then 2 else 1))) else (if x<2714 then (if x<2702 then 2 else 1) else (if x<2740 then 2 else (if x<2772 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5114 : Finset ℕ := ([1652,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5114 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5114 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5114 1768 4
  · have he : independentCachedBranchMembers5114.erase 1768=independentCachedBranchMembers5112 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5112
  · have he : independentCachedBranchMembers5114.filter (independentCachedEdge 1768)=independentCachedBranchMembers5113 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5113
def independentCachedBranchMembers5115 : Finset ℕ := ([1708,1752,2614,2646,2668,2680,2730,2762,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5115 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5115 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5115 4 (fun x => (if x<2680 then (if x<2614 then (if x<1752 then 0 else 0) else (if x<2646 then 1 else (if x<2668 then 2 else 1))) else (if x<2762 then (if x<2730 then 2 else 1) else (if x<2788 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5116 : Finset ℕ := ([1652,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5116 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5116 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5116 1692 4
  · have he : independentCachedBranchMembers5116.erase 1692=independentCachedBranchMembers5114 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5114
  · have he : independentCachedBranchMembers5116.filter (independentCachedEdge 1692)=independentCachedBranchMembers5115 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5115
def independentCachedBranchMembers5117 : Finset ℕ := ([1714,1734,2614,2620,2674,2680,2714,2730,2772,2788] : List ℕ).toFinset
theorem independentCachedBranchBound5117 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5117 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5117 4 (fun x => (if x<2680 then (if x<2614 then (if x<1734 then 0 else 0) else (if x<2620 then 1 else (if x<2674 then 2 else 2))) else (if x<2730 then (if x<2714 then 1 else 1) else (if x<2772 then 2 else (if x<2788 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5118 : Finset ℕ := ([1614,1652,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5118 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5118 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5118 1614 4
  · have he : independentCachedBranchMembers5118.erase 1614=independentCachedBranchMembers5116 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5116
  · have he : independentCachedBranchMembers5118.filter (independentCachedEdge 1614)=independentCachedBranchMembers5117 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5117
def independentCachedBranchMembers5119 : Finset ℕ := ([1714,1734,2646,2652,2662,2668,2702,2740,2762,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5119 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5119 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5119 4 (fun x => (if x<2668 then (if x<2646 then (if x<1734 then 0 else 0) else (if x<2652 then 1 else (if x<2662 then 2 else 2))) else (if x<2740 then (if x<2702 then 1 else 1) else (if x<2762 then 1 else (if x<2800 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
