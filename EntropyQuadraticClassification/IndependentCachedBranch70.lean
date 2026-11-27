/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch69
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5024 : Finset ℕ := ([1762,2788,2800,3188,3228] : List ℕ).toFinset
theorem independentCachedBranchBound5024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5024 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5024 3 (fun x => (if x<2800 then (if x<2788 then 0 else 0) else (if x<3188 then 1 else (if x<3228 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5025 : Finset ℕ := ([1652,1692,1762,2662,2674,2702,2714,2788,2800,3188,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5025 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5025 1692 3
  · have he : independentCachedBranchMembers5025.erase 1692=independentCachedBranchMembers5023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5023
  · have he : independentCachedBranchMembers5025.filter (independentCachedEdge 1692)=independentCachedBranchMembers5024 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5024
def independentCachedBranchMembers5026 : Finset ℕ := ([40,66,1582,1594,1652,1692,1708,1734,1762,2620,2646,2662,2674,2702,2714,2730,2772,2788,2800,3118,3130,3188,3228,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5026 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5026 40 4
  · have he : independentCachedBranchMembers5026.erase 40=independentCachedBranchMembers5022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5022
  · have he : independentCachedBranchMembers5026.filter (independentCachedEdge 40)=independentCachedBranchMembers5025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5025
def independentCachedBranchMembers5027 : Finset ℕ := ([40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5027 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5027 72 5
  · have he : independentCachedBranchMembers5027.erase 72=independentCachedBranchMembers5019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5019
  · have he : independentCachedBranchMembers5027.filter (independentCachedEdge 72)=independentCachedBranchMembers5026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5026
def independentCachedBranchMembers5028 : Finset ℕ := ([1614,1626,1652,1686,1708,1734,1768,2620,2646,2668,2680,2702,2714,2740,2762,2788,2800,3150,3162,3188,3222,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5028 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5028 5 (fun x => (if x<2714 then (if x<1768 then (if x<1686 then (if x<1626 then 0 else (if x<1652 then 1 else 0)) else (if x<1708 then 0 else (if x<1734 then 0 else 1))) else (if x<2668 then (if x<2620 then 1 else (if x<2646 then 2 else 0)) else (if x<2680 then 0 else (if x<2702 then 1 else 0)))) else (if x<3162 then (if x<2788 then (if x<2740 then 2 else (if x<2762 then 0 else 1)) else (if x<2800 then 1 else (if x<3150 then 2 else 3))) else (if x<3256 then (if x<3188 then 4 else (if x<3222 then 2 else 3)) else (if x<3282 then 2 else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5029 : Finset ℕ := ([1652,1768,2668,2680,2702,2714,2788,2800,3188,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5029 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5029 4 (fun x => (if x<2714 then (if x<2668 then (if x<1768 then 0 else 0) else (if x<2680 then 0 else (if x<2702 then 1 else 2))) else (if x<3188 then (if x<2788 then 1 else (if x<2800 then 2 else 0)) else (if x<3222 then 1 else (if x<3304 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5030 : Finset ℕ := ([1768,2788,2800,3188,3222] : List ℕ).toFinset
theorem independentCachedBranchBound5030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5030 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5030 3 (fun x => (if x<2800 then (if x<2788 then 0 else 0) else (if x<3188 then 1 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5031 : Finset ℕ := ([1652,1686,1768,2668,2680,2702,2714,2788,2800,3188,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5031 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5031 1686 3
  · have he : independentCachedBranchMembers5031.erase 1686=independentCachedBranchMembers5029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5029
  · have he : independentCachedBranchMembers5031.filter (independentCachedEdge 1686)=independentCachedBranchMembers5030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5030
def independentCachedBranchMembers5032 : Finset ℕ := ([66,1614,1626,1652,1686,1708,1734,1768,2620,2646,2668,2680,2702,2714,2740,2762,2788,2800,3150,3162,3188,3222,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5032 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5032 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5032 66 4
  · have he : independentCachedBranchMembers5032.erase 66=independentCachedBranchMembers5028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5028
  · have he : independentCachedBranchMembers5032.filter (independentCachedEdge 66)=independentCachedBranchMembers5031 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5031
def independentCachedBranchMembers5033 : Finset ℕ := ([1614,1626,1652,2702,2714,2740,2762,2788,2800,3150,3162,3188] : List ℕ).toFinset
theorem independentCachedBranchBound5033 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5033 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5033 4 (fun x => (if x<2762 then (if x<2702 then (if x<1626 then 0 else (if x<1652 then 1 else 0)) else (if x<2714 then 0 else (if x<2740 then 1 else 0))) else (if x<3150 then (if x<2788 then 2 else (if x<2800 then 2 else 3)) else (if x<3162 then 3 else (if x<3188 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5034 : Finset ℕ := ([40,66,1614,1626,1652,1686,1708,1734,1768,2620,2646,2668,2680,2702,2714,2740,2762,2788,2800,3150,3162,3188,3222,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5034 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5034 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5034 40 4
  · have he : independentCachedBranchMembers5034.erase 40=independentCachedBranchMembers5032 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5032
  · have he : independentCachedBranchMembers5034.filter (independentCachedEdge 40)=independentCachedBranchMembers5033 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5033
def independentCachedBranchMembers5035 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5035 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5035 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5035 34 5
  · have he : independentCachedBranchMembers5035.erase 34=independentCachedBranchMembers5027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5027
  · have he : independentCachedBranchMembers5035.filter (independentCachedEdge 34)=independentCachedBranchMembers5034 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5034
def independentCachedBranchMembers5036 : Finset ℕ := ([1594,1614,1652,1686,1708,1734,1752,1762,2620,2646,2668,2674,2702,2730,2740,2788,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5036 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5036 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5036 5 (fun x => (if x<2702 then (if x<1752 then (if x<1686 then (if x<1614 then 0 else (if x<1652 then 0 else 0)) else (if x<1708 then 0 else (if x<1734 then 0 else 1))) else (if x<2646 then (if x<1762 then 0 else (if x<2620 then 0 else 1)) else (if x<2668 then 1 else (if x<2674 then 2 else 2)))) else (if x<3228 then (if x<2788 then (if x<2730 then 1 else (if x<2740 then 2 else 2)) else (if x<3118 then 1 else (if x<3162 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5037 : Finset ℕ := ([1594,1614,1686,1762,2620,2646,2702,2788,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5037 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5037 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5037 4 (fun x => (if x<2702 then (if x<1762 then (if x<1614 then 0 else (if x<1686 then 0 else 0)) else (if x<2620 then 0 else (if x<2646 then 1 else 1))) else (if x<3256 then (if x<2788 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5038 : Finset ℕ := ([1594,1614,1642,1652,1686,1708,1734,1752,1762,2620,2646,2668,2674,2702,2730,2740,2788,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5038 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5038 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5038 1642 4
  · have he : independentCachedBranchMembers5038.erase 1642=independentCachedBranchMembers5036 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5036
  · have he : independentCachedBranchMembers5038.filter (independentCachedEdge 1642)=independentCachedBranchMembers5037 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5037
def independentCachedBranchMembers5039 : Finset ℕ := ([1594,1652,1686,1752,2620,2646,2674,2740,3162,3228,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5039 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5039 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5039 4 (fun x => (if x<2674 then (if x<1752 then (if x<1652 then 0 else (if x<1686 then 0 else 0)) else (if x<2620 then 0 else (if x<2646 then 1 else 1))) else (if x<3228 then (if x<2740 then 2 else (if x<3162 then 2 else 2)) else (if x<3256 then 2 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5040 : Finset ℕ := ([238,1594,1614,1642,1652,1686,1708,1734,1752,1762,2620,2646,2668,2674,2702,2730,2740,2788,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5040 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5040 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5040 238 4
  · have he : independentCachedBranchMembers5040.erase 238=independentCachedBranchMembers5038 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5038
  · have he : independentCachedBranchMembers5040.filter (independentCachedEdge 238)=independentCachedBranchMembers5039 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5039
def independentCachedBranchMembers5041 : Finset ℕ := ([1614,1652,1752,1762,2620,2646,2668,2730,3118,3256,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5041 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5041 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5041 4 (fun x => (if x<2668 then (if x<1762 then (if x<1652 then 0 else (if x<1752 then 0 else 0)) else (if x<2620 then 0 else (if x<2646 then 1 else 1))) else (if x<3256 then (if x<2730 then 2 else (if x<3118 then 2 else 2)) else (if x<3282 then 1 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5042 : Finset ℕ := ([132,238,1594,1614,1642,1652,1686,1708,1734,1752,1762,2620,2646,2668,2674,2702,2730,2740,2788,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5042 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5042 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5042 132 4
  · have he : independentCachedBranchMembers5042.erase 132=independentCachedBranchMembers5040 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5040
  · have he : independentCachedBranchMembers5042.filter (independentCachedEdge 132)=independentCachedBranchMembers5041 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5041
def independentCachedBranchMembers5043 : Finset ℕ := ([1594,1652,1686,1752,2668,2702,2730,2788,3118,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5043 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5043 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5043 4 (fun x => (if x<2730 then (if x<1752 then (if x<1652 then 0 else (if x<1686 then 0 else 0)) else (if x<2668 then 0 else (if x<2702 then 1 else 1))) else (if x<3238 then (if x<2788 then 2 else (if x<3118 then 2 else 1)) else (if x<3276 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5044 : Finset ℕ := ([66,132,238,1594,1614,1642,1652,1686,1708,1734,1752,1762,2620,2646,2668,2674,2702,2730,2740,2788,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5044 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5044 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5044 66 4
  · have he : independentCachedBranchMembers5044.erase 66=independentCachedBranchMembers5042 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5042
  · have he : independentCachedBranchMembers5044.filter (independentCachedEdge 66)=independentCachedBranchMembers5043 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5043
def independentCachedBranchMembers5045 : Finset ℕ := ([1614,1652,1752,1762,2674,2702,2740,2788,3162,3228,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5045 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5045 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5045 4 (fun x => (if x<2740 then (if x<1762 then (if x<1652 then 0 else (if x<1752 then 0 else 0)) else (if x<2674 then 0 else (if x<2702 then 1 else 2))) else (if x<3228 then (if x<2788 then 1 else (if x<3162 then 2 else 1)) else (if x<3238 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5046 : Finset ℕ := ([40,66,132,238,1594,1614,1642,1652,1686,1708,1734,1752,1762,2620,2646,2668,2674,2702,2730,2740,2788,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5046 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5046 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5046 40 4
  · have he : independentCachedBranchMembers5046.erase 40=independentCachedBranchMembers5044 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5044
  · have he : independentCachedBranchMembers5046.filter (independentCachedEdge 40)=independentCachedBranchMembers5045 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5045
def independentCachedBranchMembers5047 : Finset ℕ := ([40,66,132,238,1594,1614,1686,1762,2620,2646,2702,2788,3118,3162,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5047 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5047 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5047 4 (fun x => (if x<2620 then (if x<1594 then (if x<132 then (if x<66 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1686 then (if x<1614 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2646 then 2 else 2) else (if x<2788 then 2 else 2)) else (if x<3228 then (if x<3162 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5048 : Finset ℕ := ([40,66,132,238,1594,1614,1642,1652,1686,1708,1714,1734,1752,1762,2620,2646,2668,2674,2702,2730,2740,2788,3118,3162,3228,3238,3256,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5048 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5048 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5048 1714 4
  · have he : independentCachedBranchMembers5048.erase 1714=independentCachedBranchMembers5046 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5046
  · have he : independentCachedBranchMembers5048.filter (independentCachedEdge 1714)=independentCachedBranchMembers5047 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5047
def independentCachedBranchMembers5049 : Finset ℕ := ([34,40,66,72,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5049 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5049 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5049 3288 5
  · have he : independentCachedBranchMembers5049.erase 3288=independentCachedBranchMembers5035 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5035
  · have he : independentCachedBranchMembers5049.filter (independentCachedEdge 3288)=independentCachedBranchMembers5048 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5048
def independentCachedBranchMembers5050 : Finset ℕ := ([1582,1626,1652,1692,1714,1734,1752,1768,2614,2652,2668,2674,2714,2730,2740,2800,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5050 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5050 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5050 5 (fun x => (if x<2714 then (if x<1752 then (if x<1692 then (if x<1626 then 0 else (if x<1652 then 0 else 0)) else (if x<1714 then 0 else (if x<1734 then 0 else 0))) else (if x<2652 then (if x<1768 then 1 else (if x<2614 then 0 else 1)) else (if x<2668 then 1 else (if x<2674 then 2 else 2)))) else (if x<3222 then (if x<2800 then (if x<2730 then 1 else (if x<2740 then 2 else 2)) else (if x<3130 then 1 else (if x<3150 then 3 else 3))) else (if x<3276 then (if x<3238 then 3 else (if x<3256 then 4 else 4)) else (if x<3282 then 4 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5051 : Finset ℕ := ([1582,1626,1692,1768,2614,2652,2714,2800,3238,3256,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5051 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5051 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5051 4 (fun x => (if x<2714 then (if x<1768 then (if x<1626 then 0 else (if x<1692 then 0 else 0)) else (if x<2614 then 0 else (if x<2652 then 1 else 1))) else (if x<3256 then (if x<2800 then 1 else (if x<3238 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5052 : Finset ℕ := ([1582,1626,1642,1652,1692,1714,1734,1752,1768,2614,2652,2668,2674,2714,2730,2740,2800,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5052 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5052 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5052 1642 4
  · have he : independentCachedBranchMembers5052.erase 1642=independentCachedBranchMembers5050 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5050
  · have he : independentCachedBranchMembers5052.filter (independentCachedEdge 1642)=independentCachedBranchMembers5051 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5051
def independentCachedBranchMembers5053 : Finset ℕ := ([1582,1652,1692,1734,2614,2652,2668,2740,3150,3222,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5053 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5053 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5053 4 (fun x => (if x<2668 then (if x<1734 then (if x<1652 then 0 else (if x<1692 then 0 else 0)) else (if x<2614 then 0 else (if x<2652 then 1 else 1))) else (if x<3222 then (if x<2740 then 2 else (if x<3150 then 2 else 2)) else (if x<3238 then 2 else (if x<3276 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5054 : Finset ℕ := ([250,1582,1626,1642,1652,1692,1714,1734,1752,1768,2614,2652,2668,2674,2714,2730,2740,2800,3130,3150,3222,3238,3256,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5054 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5054 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5054 250 4
  · have he : independentCachedBranchMembers5054.erase 250=independentCachedBranchMembers5052 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5052
  · have he : independentCachedBranchMembers5054.filter (independentCachedEdge 250)=independentCachedBranchMembers5053 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5053
def independentCachedBranchMembers5055 : Finset ℕ := ([1626,1652,1734,1768,2614,2652,2674,2730,3130,3238,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5055 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5055 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5055 4 (fun x => (if x<2674 then (if x<1768 then (if x<1652 then 0 else (if x<1734 then 0 else 0)) else (if x<2614 then 0 else (if x<2652 then 1 else 1))) else (if x<3238 then (if x<2730 then 2 else (if x<3130 then 2 else 2)) else (if x<3276 then 1 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
