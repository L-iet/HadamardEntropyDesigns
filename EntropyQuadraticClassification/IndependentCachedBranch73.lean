/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch72
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5120 : Finset ℕ := ([1594,1614,1652,1692,1708,1714,1734,1752,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5120 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5120 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5120 1594 4
  · have he : independentCachedBranchMembers5120.erase 1594=independentCachedBranchMembers5118 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5118
  · have he : independentCachedBranchMembers5120.filter (independentCachedEdge 1594)=independentCachedBranchMembers5119 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5119
def independentCachedBranchMembers5121 : Finset ℕ := ([1692,1714,1734,1768,2614,2646,2668,2680,2702,2714,2740,2772] : List ℕ).toFinset
theorem independentCachedBranchBound5121 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5121 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5121 4 (fun x => (if x<2668 then (if x<1768 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2614 then 0 else (if x<2646 then 1 else 2))) else (if x<2714 then (if x<2680 then 1 else (if x<2702 then 2 else 1)) else (if x<2740 then 2 else (if x<2772 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5122 : Finset ℕ := ([1594,1614,1652,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5122 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5122 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5122 1762 4
  · have he : independentCachedBranchMembers5122.erase 1762=independentCachedBranchMembers5120 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5120
  · have he : independentCachedBranchMembers5122.filter (independentCachedEdge 1762)=independentCachedBranchMembers5121 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5121
def independentCachedBranchMembers5123 : Finset ℕ := ([1692,1714,1734,1768,2620,2652,2662,2674,2730,2762,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5123 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5123 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5123 4 (fun x => (if x<2662 then (if x<1768 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<2620 then 0 else (if x<2652 then 1 else 2))) else (if x<2762 then (if x<2674 then 1 else (if x<2730 then 2 else 1)) else (if x<2788 then 2 else (if x<2800 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5124 : Finset ℕ := ([1594,1614,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5124 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5124 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5124 1686 4
  · have he : independentCachedBranchMembers5124.erase 1686=independentCachedBranchMembers5122 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5122
  · have he : independentCachedBranchMembers5124.filter (independentCachedEdge 1686)=independentCachedBranchMembers5123 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5123
def independentCachedBranchMembers5125 : Finset ℕ := ([1594,1614,1708,1752,2614,2620,2662,2668,2702,2730,2772,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5125 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5125 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5125 4 (fun x => (if x<2662 then (if x<1752 then (if x<1614 then 0 else (if x<1708 then 0 else 0)) else (if x<2614 then 0 else (if x<2620 then 1 else 2))) else (if x<2730 then (if x<2668 then 2 else (if x<2702 then 1 else 1)) else (if x<2772 then 2 else (if x<2800 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5126 : Finset ℕ := ([1594,1614,1626,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5126 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5126 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5126 1626 4
  · have he : independentCachedBranchMembers5126.erase 1626=independentCachedBranchMembers5124 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5124
  · have he : independentCachedBranchMembers5126.filter (independentCachedEdge 1626)=independentCachedBranchMembers5125 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5125
def independentCachedBranchMembers5127 : Finset ℕ := ([1594,1614,1708,1752,2646,2652,2674,2680,2714,2740,2762,2788] : List ℕ).toFinset
theorem independentCachedBranchBound5127 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5127 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5127 4 (fun x => (if x<2674 then (if x<1752 then (if x<1614 then 0 else (if x<1708 then 0 else 0)) else (if x<2646 then 0 else (if x<2652 then 1 else 2))) else (if x<2740 then (if x<2680 then 2 else (if x<2714 then 1 else 1)) else (if x<2762 then 1 else (if x<2788 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5128 : Finset ℕ := ([1582,1594,1614,1626,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5128 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5128 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5128 1582 4
  · have he : independentCachedBranchMembers5128.erase 1582=independentCachedBranchMembers5126 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5126
  · have he : independentCachedBranchMembers5128.filter (independentCachedEdge 1582)=independentCachedBranchMembers5127 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5127
def independentCachedBranchMembers5129 : Finset ℕ := ([1582,1594,1614,1626,1686,1692,1762,1768,2614,2620,2646,2652,2702,2714,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5129 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5129 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5129 4 (fun x => (if x<2614 then (if x<1686 then (if x<1614 then (if x<1594 then 0 else 1) else (if x<1626 then 1 else 0)) else (if x<1762 then (if x<1692 then 0 else 1) else (if x<1768 then 0 else 1))) else (if x<2702 then (if x<2646 then (if x<2620 then 2 else 3) else (if x<2652 then 3 else 2)) else (if x<2788 then (if x<2714 then 2 else 3) else (if x<2800 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5130 : Finset ℕ := ([1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800] : List ℕ).toFinset
theorem independentCachedBranchBound5130 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5130 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5130 1642 4
  · have he : independentCachedBranchMembers5130.erase 1642=independentCachedBranchMembers5128 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5128
  · have he : independentCachedBranchMembers5130.filter (independentCachedEdge 1642)=independentCachedBranchMembers5129 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5129
def independentCachedBranchMembers5131 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5131 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5131 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5131 3072 5
  · have he : independentCachedBranchMembers5131.erase 3072=independentCachedBranchMembers5111 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5111
  · have he : independentCachedBranchMembers5131.filter (independentCachedEdge 3072)=independentCachedBranchMembers5130 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5130
def independentCachedBranchMembers5132 : Finset ℕ := ([132,238,1582,1626,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3178,3188,3228,3238,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5132 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5132 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5132 5 (fun x => (if x<2680 then (if x<1714 then (if x<1626 then (if x<238 then 0 else (if x<1582 then 0 else 1)) else (if x<1686 then 1 else (if x<1708 then 1 else 0))) else (if x<1762 then (if x<1734 then 2 else (if x<1752 then 0 else 2)) else (if x<2652 then (if x<2614 then 1 else 2) else (if x<2662 then 2 else 3)))) else (if x<3178 then (if x<2740 then (if x<2702 then 3 else (if x<2730 then 0 else 3)) else (if x<3130 then (if x<2788 then 3 else 0) else (if x<3150 then 4 else 4))) else (if x<3238 then (if x<3188 then 1 else (if x<3228 then 3 else 4)) else (if x<3282 then (if x<3276 then 0 else 0) else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5133 : Finset ℕ := ([1582,1708,1734,1762,2662,2702,2730,2788,3130,3188,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5133 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5133 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5133 4 (fun x => (if x<2730 then (if x<1762 then (if x<1708 then 0 else (if x<1734 then 1 else 0)) else (if x<2662 then 1 else (if x<2702 then 0 else 0))) else (if x<3188 then (if x<2788 then 1 else (if x<3130 then 1 else 2)) else (if x<3228 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5134 : Finset ℕ := ([72,132,238,1582,1626,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3178,3188,3228,3238,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5134 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5134 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5134 72 4
  · have he : independentCachedBranchMembers5134.erase 72=independentCachedBranchMembers5132 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5132
  · have he : independentCachedBranchMembers5134.filter (independentCachedEdge 72)=independentCachedBranchMembers5133 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5133
def independentCachedBranchMembers5135 : Finset ℕ := ([1626,1686,1708,1734,2680,2702,2740,2788,3150,3188,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5135 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5135 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5135 4 (fun x => (if x<2740 then (if x<1734 then (if x<1686 then 0 else (if x<1708 then 0 else 1)) else (if x<2680 then 1 else (if x<2702 then 0 else 1))) else (if x<3188 then (if x<2788 then 0 else (if x<3150 then 1 else 2)) else (if x<3282 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5136 : Finset ℕ := ([34,72,132,238,1582,1626,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3178,3188,3228,3238,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5136 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5136 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5136 34 4
  · have he : independentCachedBranchMembers5136.erase 34=independentCachedBranchMembers5134 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5134
  · have he : independentCachedBranchMembers5136.filter (independentCachedEdge 34)=independentCachedBranchMembers5135 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5135
def independentCachedBranchMembers5137 : Finset ℕ := ([34,72,132,238,1582,1626,1686,1762,2614,2652,2702,2788,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5137 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5137 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5137 4 (fun x => (if x<2614 then (if x<1582 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1686 then (if x<1626 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3130 then (if x<2702 then (if x<2652 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5138 : Finset ℕ := ([34,72,132,238,1582,1626,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2702,2730,2740,2788,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5138 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5138 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5138 3256 4
  · have he : independentCachedBranchMembers5138.erase 3256=independentCachedBranchMembers5136 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5136
  · have he : independentCachedBranchMembers5138.filter (independentCachedEdge 3256)=independentCachedBranchMembers5137 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5137
def independentCachedBranchMembers5139 : Finset ℕ := ([34,72,132,238,1708,1714,1734,1752,2662,2680,2730,2740,3130,3150,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5139 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5139 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5139 4 (fun x => (if x<2662 then (if x<1708 then (if x<132 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3130 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3228 then (if x<3150 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5140 : Finset ℕ := ([34,72,132,238,1582,1626,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2702,2730,2740,2788,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5140 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5140 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5140 3102 4
  · have he : independentCachedBranchMembers5140.erase 3102=independentCachedBranchMembers5138 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5138
  · have he : independentCachedBranchMembers5140.filter (independentCachedEdge 3102)=independentCachedBranchMembers5139 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5139
def independentCachedBranchMembers5141 : Finset ℕ := ([1582,1626,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2702,2730,2740,2788] : List ℕ).toFinset
theorem independentCachedBranchBound5141 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5141 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5141 4 (fun x => (if x<2614 then (if x<1714 then (if x<1686 then (if x<1626 then 0 else 0) else (if x<1708 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 1) else (if x<1762 then 1 else 0))) else (if x<2702 then (if x<2662 then (if x<2652 then 2 else 2) else (if x<2680 then 3 else 3)) else (if x<2740 then (if x<2730 then 2 else 3) else (if x<2788 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5142 : Finset ℕ := ([34,72,132,238,1582,1626,1686,1708,1714,1734,1752,1762,2614,2652,2662,2680,2702,2730,2740,2788,3072,3102,3130,3150,3178,3188,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5142 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5142 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5142 3072 4
  · have he : independentCachedBranchMembers5142.erase 3072=independentCachedBranchMembers5140 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5140
  · have he : independentCachedBranchMembers5142.filter (independentCachedEdge 3072)=independentCachedBranchMembers5141 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5141
def independentCachedBranchMembers5143 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1746,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3072,3102,3118,3130,3150,3162,3178,3188,3222,3228,3238,3244,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5143 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5143 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5143 1746 5
  · have he : independentCachedBranchMembers5143.erase 1746=independentCachedBranchMembers5131 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5131
  · have he : independentCachedBranchMembers5143.filter (independentCachedEdge 1746)=independentCachedBranchMembers5142 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5142
def independentCachedBranchMembers5144 : Finset ℕ := ([144,250,1594,1614,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3178,3188,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5144 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5144 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5144 5 (fun x => (if x<2680 then (if x<1714 then (if x<1614 then (if x<250 then 0 else (if x<1594 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 1 else 2))) else (if x<1768 then (if x<1734 then 0 else (if x<1752 then 2 else 0)) else (if x<2646 then (if x<2620 then 1 else 2) else (if x<2662 then 2 else 3)))) else (if x<3178 then (if x<2740 then (if x<2714 then 3 else (if x<2730 then 0 else 3)) else (if x<3118 then (if x<2800 then 3 else 0) else (if x<3162 then 4 else 4))) else (if x<3256 then (if x<3188 then 1 else (if x<3222 then 3 else 4)) else (if x<3282 then (if x<3276 then 0 else 1) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5145 : Finset ℕ := ([1594,1714,1752,1768,2680,2714,2730,2800,3118,3188,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5145 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5145 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5145 4 (fun x => (if x<2730 then (if x<1768 then (if x<1714 then 0 else (if x<1752 then 1 else 0)) else (if x<2680 then 1 else (if x<2714 then 0 else 0))) else (if x<3188 then (if x<2800 then 1 else (if x<3118 then 1 else 2)) else (if x<3222 then 2 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5146 : Finset ℕ := ([66,144,250,1594,1614,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3178,3188,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5146 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5146 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5146 66 4
  · have he : independentCachedBranchMembers5146.erase 66=independentCachedBranchMembers5144 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5144
  · have he : independentCachedBranchMembers5146.filter (independentCachedEdge 66)=independentCachedBranchMembers5145 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5145
def independentCachedBranchMembers5147 : Finset ℕ := ([1614,1692,1714,1752,2662,2714,2740,2800,3162,3188,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5147 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5147 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5147 4 (fun x => (if x<2740 then (if x<1752 then (if x<1692 then 0 else (if x<1714 then 0 else 1)) else (if x<2662 then 1 else (if x<2714 then 0 else 1))) else (if x<3188 then (if x<2800 then 0 else (if x<3162 then 1 else 2)) else (if x<3276 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5148 : Finset ℕ := ([40,66,144,250,1594,1614,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3178,3188,3222,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5148 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5148 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5148 40 4
  · have he : independentCachedBranchMembers5148.erase 40=independentCachedBranchMembers5146 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5146
  · have he : independentCachedBranchMembers5148.filter (independentCachedEdge 40)=independentCachedBranchMembers5147 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5147
def independentCachedBranchMembers5149 : Finset ℕ := ([40,66,144,250,1594,1614,1692,1768,2620,2646,2714,2800,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5149 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5149 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5149 4 (fun x => (if x<2620 then (if x<1594 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1692 then (if x<1614 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2646 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5150 : Finset ℕ := ([40,66,144,250,1594,1614,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2714,2730,2740,2800,3118,3162,3178,3188,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5150 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5150 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5150 3238 4
  · have he : independentCachedBranchMembers5150.erase 3238=independentCachedBranchMembers5148 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5148
  · have he : independentCachedBranchMembers5150.filter (independentCachedEdge 3238)=independentCachedBranchMembers5149 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5149
def independentCachedBranchMembers5151 : Finset ℕ := ([40,66,144,250,1708,1714,1734,1752,2662,2680,2730,2740,3118,3162,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5151 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5151 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5151 4 (fun x => (if x<2662 then (if x<1708 then (if x<144 then (if x<66 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1752 then 1 else 1))) else (if x<3118 then (if x<2730 then (if x<2680 then 2 else 2) else (if x<2740 then 2 else 2)) else (if x<3222 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
