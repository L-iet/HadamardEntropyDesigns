/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch70
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5056 : Finset ℕ := ([144,250,1582,1626,1642,1652,1692,1714,1734,1752,1768,2614,2652,2668,2674,2714,2730,2740,2800,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5056 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5056 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5056 144 4
  · have he : independentCachedBranchMembers5056.erase 144=independentCachedBranchMembers5054 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5054
  · have he : independentCachedBranchMembers5056.filter (independentCachedEdge 144)=independentCachedBranchMembers5055 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5055
def independentCachedBranchMembers5057 : Finset ℕ := ([1582,1652,1692,1734,2674,2714,2730,2800,3130,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5057 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5057 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5057 4 (fun x => (if x<2730 then (if x<1734 then (if x<1652 then 0 else (if x<1692 then 0 else 0)) else (if x<2674 then 0 else (if x<2714 then 1 else 1))) else (if x<3256 then (if x<2800 then 2 else (if x<3130 then 2 else 1)) else (if x<3282 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5058 : Finset ℕ := ([72,144,250,1582,1626,1642,1652,1692,1714,1734,1752,1768,2614,2652,2668,2674,2714,2730,2740,2800,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5058 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5058 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5058 72 4
  · have he : independentCachedBranchMembers5058.erase 72=independentCachedBranchMembers5056 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5056
  · have he : independentCachedBranchMembers5058.filter (independentCachedEdge 72)=independentCachedBranchMembers5057 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5057
def independentCachedBranchMembers5059 : Finset ℕ := ([1626,1652,1734,1768,2668,2714,2740,2800,3150,3222,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5059 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5059 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5059 4 (fun x => (if x<2740 then (if x<1768 then (if x<1652 then 0 else (if x<1734 then 0 else 0)) else (if x<2668 then 0 else (if x<2714 then 1 else 2))) else (if x<3222 then (if x<2800 then 1 else (if x<3150 then 2 else 1)) else (if x<3256 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5060 : Finset ℕ := ([34,72,144,250,1582,1626,1642,1652,1692,1714,1734,1752,1768,2614,2652,2668,2674,2714,2730,2740,2800,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5060 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5060 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5060 34 4
  · have he : independentCachedBranchMembers5060.erase 34=independentCachedBranchMembers5058 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5058
  · have he : independentCachedBranchMembers5060.filter (independentCachedEdge 34)=independentCachedBranchMembers5059 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5059
def independentCachedBranchMembers5061 : Finset ℕ := ([34,72,144,250,1582,1626,1692,1768,2614,2652,2714,2800,3130,3150,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5061 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5061 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5061 4 (fun x => (if x<2614 then (if x<1582 then (if x<144 then (if x<72 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1692 then (if x<1626 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2652 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3222 then (if x<3150 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5062 : Finset ℕ := ([34,72,144,250,1582,1626,1642,1652,1692,1708,1714,1734,1752,1768,2614,2652,2668,2674,2714,2730,2740,2800,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5062 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5062 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5062 1708 4
  · have he : independentCachedBranchMembers5062.erase 1708=independentCachedBranchMembers5060 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5060
  · have he : independentCachedBranchMembers5062.filter (independentCachedEdge 1708)=independentCachedBranchMembers5061 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5061
def independentCachedBranchMembers5063 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5063 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5063 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5063 3270 5
  · have he : independentCachedBranchMembers5063.erase 3270=independentCachedBranchMembers5049 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5049
  · have he : independentCachedBranchMembers5063.filter (independentCachedEdge 3270)=independentCachedBranchMembers5062 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5062
def independentCachedBranchMembers5064 : Finset ℕ := ([1582,1626,1652,1692,1708,1714,1734,1768,2620,2646,2662,2680,2702,2762,2772,2788,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5064 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5064 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5064 5 (fun x => (if x<2702 then (if x<1734 then (if x<1692 then (if x<1626 then 0 else (if x<1652 then 0 else 0)) else (if x<1708 then 0 else (if x<1714 then 1 else 0))) else (if x<2646 then (if x<1768 then 0 else (if x<2620 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3222 then (if x<2788 then (if x<2762 then 1 else (if x<2772 then 2 else 2)) else (if x<3130 then 1 else (if x<3150 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5065 : Finset ℕ := ([1582,1626,1692,1768,2620,2646,2702,2788,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5065 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5065 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5065 4 (fun x => (if x<2702 then (if x<1768 then (if x<1626 then 0 else (if x<1692 then 0 else 0)) else (if x<2620 then 0 else (if x<2646 then 1 else 1))) else (if x<3256 then (if x<2788 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5066 : Finset ℕ := ([1582,1626,1642,1652,1692,1708,1714,1734,1768,2620,2646,2662,2680,2702,2762,2772,2788,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5066 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5066 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5066 1642 4
  · have he : independentCachedBranchMembers5066.erase 1642=independentCachedBranchMembers5064 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5064
  · have he : independentCachedBranchMembers5066.filter (independentCachedEdge 1642)=independentCachedBranchMembers5065 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5065
def independentCachedBranchMembers5067 : Finset ℕ := ([1626,1652,1692,1714,2620,2646,2680,2772,3130,3222,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5067 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5067 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5067 4 (fun x => (if x<2680 then (if x<1714 then (if x<1652 then 0 else (if x<1692 then 0 else 0)) else (if x<2620 then 0 else (if x<2646 then 1 else 1))) else (if x<3222 then (if x<2772 then 2 else (if x<3130 then 2 else 2)) else (if x<3256 then 2 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5068 : Finset ℕ := ([238,1582,1626,1642,1652,1692,1708,1714,1734,1768,2620,2646,2662,2680,2702,2762,2772,2788,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5068 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5068 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5068 238 4
  · have he : independentCachedBranchMembers5068.erase 238=independentCachedBranchMembers5066 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5066
  · have he : independentCachedBranchMembers5068.filter (independentCachedEdge 238)=independentCachedBranchMembers5067 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5067
def independentCachedBranchMembers5069 : Finset ℕ := ([1582,1652,1714,1768,2620,2646,2662,2762,3150,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5069 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5069 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5069 4 (fun x => (if x<2662 then (if x<1768 then (if x<1652 then 0 else (if x<1714 then 0 else 0)) else (if x<2620 then 0 else (if x<2646 then 1 else 1))) else (if x<3256 then (if x<2762 then 2 else (if x<3150 then 2 else 2)) else (if x<3282 then 1 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5070 : Finset ℕ := ([132,238,1582,1626,1642,1652,1692,1708,1714,1734,1768,2620,2646,2662,2680,2702,2762,2772,2788,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5070 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5070 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5070 132 4
  · have he : independentCachedBranchMembers5070.erase 132=independentCachedBranchMembers5068 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5068
  · have he : independentCachedBranchMembers5070.filter (independentCachedEdge 132)=independentCachedBranchMembers5069 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5069
def independentCachedBranchMembers5071 : Finset ℕ := ([1582,1652,1714,1768,2680,2702,2772,2788,3130,3222,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5071 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5071 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5071 4 (fun x => (if x<2772 then (if x<1768 then (if x<1652 then 0 else (if x<1714 then 0 else 0)) else (if x<2680 then 0 else (if x<2702 then 1 else 2))) else (if x<3222 then (if x<2788 then 1 else (if x<3130 then 2 else 1)) else (if x<3238 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5072 : Finset ℕ := ([66,132,238,1582,1626,1642,1652,1692,1708,1714,1734,1768,2620,2646,2662,2680,2702,2762,2772,2788,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5072 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5072 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5072 66 4
  · have he : independentCachedBranchMembers5072.erase 66=independentCachedBranchMembers5070 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5070
  · have he : independentCachedBranchMembers5072.filter (independentCachedEdge 66)=independentCachedBranchMembers5071 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5071
def independentCachedBranchMembers5073 : Finset ℕ := ([1626,1652,1692,1714,2662,2702,2762,2788,3150,3238,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5073 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5073 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5073 4 (fun x => (if x<2762 then (if x<1714 then (if x<1652 then 0 else (if x<1692 then 0 else 0)) else (if x<2662 then 0 else (if x<2702 then 1 else 1))) else (if x<3238 then (if x<2788 then 2 else (if x<3150 then 2 else 1)) else (if x<3276 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5074 : Finset ℕ := ([40,66,132,238,1582,1626,1642,1652,1692,1708,1714,1734,1768,2620,2646,2662,2680,2702,2762,2772,2788,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5074 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5074 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5074 40 4
  · have he : independentCachedBranchMembers5074.erase 40=independentCachedBranchMembers5072 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5072
  · have he : independentCachedBranchMembers5074.filter (independentCachedEdge 40)=independentCachedBranchMembers5073 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5073
def independentCachedBranchMembers5075 : Finset ℕ := ([40,66,132,238,1582,1626,1692,1768,2620,2646,2702,2788,3130,3150,3222,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5075 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5075 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5075 4 (fun x => (if x<2620 then (if x<1582 then (if x<132 then (if x<66 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1692 then (if x<1626 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3130 then (if x<2702 then (if x<2646 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3222 then (if x<3150 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5076 : Finset ℕ := ([40,66,132,238,1582,1626,1642,1652,1692,1708,1714,1734,1752,1768,2620,2646,2662,2680,2702,2762,2772,2788,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5076 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5076 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5076 1752 4
  · have he : independentCachedBranchMembers5076.erase 1752=independentCachedBranchMembers5074 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5074
  · have he : independentCachedBranchMembers5076.filter (independentCachedEdge 1752)=independentCachedBranchMembers5075 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5075
def independentCachedBranchMembers5077 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3250,3256,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5077 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5077 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5077 3250 5
  · have he : independentCachedBranchMembers5077.erase 3250=independentCachedBranchMembers5063 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5063
  · have he : independentCachedBranchMembers5077.filter (independentCachedEdge 3250)=independentCachedBranchMembers5076 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5076
def independentCachedBranchMembers5078 : Finset ℕ := ([1594,1614,1652,1686,1708,1714,1752,1762,2614,2652,2662,2680,2714,2762,2772,2800,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5078 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5078 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5078 5 (fun x => (if x<2714 then (if x<1752 then (if x<1686 then (if x<1614 then 0 else (if x<1652 then 0 else 0)) else (if x<1708 then 0 else (if x<1714 then 0 else 1))) else (if x<2652 then (if x<1762 then 0 else (if x<2614 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3228 then (if x<2800 then (if x<2762 then 1 else (if x<2772 then 2 else 2)) else (if x<3118 then 1 else (if x<3162 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5079 : Finset ℕ := ([1594,1614,1686,1762,2614,2652,2714,2800,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5079 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5079 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5079 4 (fun x => (if x<2714 then (if x<1762 then (if x<1614 then 0 else (if x<1686 then 0 else 0)) else (if x<2614 then 0 else (if x<2652 then 1 else 1))) else (if x<3256 then (if x<2800 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5080 : Finset ℕ := ([1594,1614,1642,1652,1686,1708,1714,1752,1762,2614,2652,2662,2680,2714,2762,2772,2800,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5080 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5080 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5080 1642 4
  · have he : independentCachedBranchMembers5080.erase 1642=independentCachedBranchMembers5078 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5078
  · have he : independentCachedBranchMembers5080.filter (independentCachedEdge 1642)=independentCachedBranchMembers5079 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5079
def independentCachedBranchMembers5081 : Finset ℕ := ([1614,1652,1686,1708,2614,2652,2662,2772,3118,3228,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5081 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5081 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5081 4 (fun x => (if x<2662 then (if x<1708 then (if x<1652 then 0 else (if x<1686 then 0 else 0)) else (if x<2614 then 0 else (if x<2652 then 1 else 1))) else (if x<3228 then (if x<2772 then 2 else (if x<3118 then 2 else 2)) else (if x<3238 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5082 : Finset ℕ := ([250,1594,1614,1642,1652,1686,1708,1714,1752,1762,2614,2652,2662,2680,2714,2762,2772,2800,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5082 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5082 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5082 250 4
  · have he : independentCachedBranchMembers5082.erase 250=independentCachedBranchMembers5080 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5080
  · have he : independentCachedBranchMembers5082.filter (independentCachedEdge 250)=independentCachedBranchMembers5081 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5081
def independentCachedBranchMembers5083 : Finset ℕ := ([1594,1652,1708,1762,2614,2652,2680,2762,3162,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5083 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5083 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5083 4 (fun x => (if x<2680 then (if x<1762 then (if x<1652 then 0 else (if x<1708 then 0 else 0)) else (if x<2614 then 0 else (if x<2652 then 1 else 1))) else (if x<3238 then (if x<2762 then 2 else (if x<3162 then 2 else 2)) else (if x<3276 then 1 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5084 : Finset ℕ := ([144,250,1594,1614,1642,1652,1686,1708,1714,1752,1762,2614,2652,2662,2680,2714,2762,2772,2800,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5084 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5084 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5084 144 4
  · have he : independentCachedBranchMembers5084.erase 144=independentCachedBranchMembers5082 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5082
  · have he : independentCachedBranchMembers5084.filter (independentCachedEdge 144)=independentCachedBranchMembers5083 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5083
def independentCachedBranchMembers5085 : Finset ℕ := ([1594,1652,1708,1762,2662,2714,2772,2800,3118,3228,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5085 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5085 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5085 4 (fun x => (if x<2772 then (if x<1762 then (if x<1652 then 0 else (if x<1708 then 0 else 0)) else (if x<2662 then 0 else (if x<2714 then 1 else 2))) else (if x<3228 then (if x<2800 then 1 else (if x<3118 then 2 else 1)) else (if x<3256 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5086 : Finset ℕ := ([72,144,250,1594,1614,1642,1652,1686,1708,1714,1752,1762,2614,2652,2662,2680,2714,2762,2772,2800,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5086 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5086 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5086 72 4
  · have he : independentCachedBranchMembers5086.erase 72=independentCachedBranchMembers5084 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5084
  · have he : independentCachedBranchMembers5086.filter (independentCachedEdge 72)=independentCachedBranchMembers5085 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5085
def independentCachedBranchMembers5087 : Finset ℕ := ([1614,1652,1686,1708,2680,2714,2762,2800,3162,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5087 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5087 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5087 4 (fun x => (if x<2762 then (if x<1708 then (if x<1652 then 0 else (if x<1686 then 0 else 0)) else (if x<2680 then 0 else (if x<2714 then 1 else 1))) else (if x<3256 then (if x<2800 then 2 else (if x<3162 then 2 else 1)) else (if x<3282 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
