/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch90
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5696 : Finset ℕ := ([1642,1652,1702,1708,1714,1720,1734,1752,3118,3130,3150,3162,3174,3180,3186,3192,3222,3228,3242,3252,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5696 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5696 5 (fun x => (if x<3174 then (if x<1734 then (if x<1708 then (if x<1652 then 0 else (if x<1702 then 0 else 0)) else (if x<1714 then 1 else (if x<1720 then 1 else 0))) else (if x<3130 then (if x<1752 then 1 else (if x<3118 then 1 else 2)) else (if x<3150 then 3 else (if x<3162 then 3 else 2)))) else (if x<3242 then (if x<3192 then (if x<3180 then 0 else (if x<3186 then 4 else 4)) else (if x<3222 then 0 else (if x<3228 then 2 else 3))) else (if x<3284 then (if x<3252 then 0 else (if x<3274 then 0 else 4)) else (if x<3298 then 4 else (if x<3304 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5697 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5697 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5697 3178 5
  · have he : independentCachedBranchMembers5697.erase 3178=independentCachedBranchMembers5695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5695
  · have he : independentCachedBranchMembers5697.filter (independentCachedEdge 3178)=independentCachedBranchMembers5696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5696
def independentCachedBranchMembers5698 : Finset ℕ := ([1652,1714,1752,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5698 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5698 5 (fun x => (if x<3178 then (if x<3130 then (if x<1752 then (if x<1714 then 0 else 0) else (if x<3072 then 0 else (if x<3126 then 1 else 0))) else (if x<3162 then (if x<3132 then 1 else (if x<3158 then 2 else 1)) else (if x<3164 then 2 else (if x<3174 then 0 else 2)))) else (if x<3242 then (if x<3226 then (if x<3180 then 3 else (if x<3222 then 1 else 2)) else (if x<3228 then 0 else (if x<3238 then 1 else 1))) else (if x<3274 then (if x<3244 then 2 else (if x<3270 then 3 else 3)) else (if x<3276 then 1 else (if x<3312 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5699 : Finset ℕ := ([1652,1752,3072,3126,3132,3162,3174,3180,3226,3238,3244,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5699 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5699 4 (fun x => (if x<3174 then (if x<3126 then (if x<1752 then 0 else (if x<3072 then 0 else 1)) else (if x<3132 then 0 else (if x<3162 then 1 else 1))) else (if x<3238 then (if x<3180 then 1 else (if x<3226 then 2 else 0)) else (if x<3244 then 2 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5700 : Finset ℕ := ([1652,1714,1748,1752,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5700 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5700 1748 4
  · have he : independentCachedBranchMembers5700.erase 1748=independentCachedBranchMembers5698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5698
  · have he : independentCachedBranchMembers5700.filter (independentCachedEdge 1748)=independentCachedBranchMembers5699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5699
def independentCachedBranchMembers5701 : Finset ℕ := ([1714,1752,3072,3126,3162,3164,3178,3180,3222,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5701 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5701 4 (fun x => (if x<3178 then (if x<3126 then (if x<1752 then 0 else (if x<3072 then 0 else 1)) else (if x<3162 then 0 else (if x<3164 then 1 else 0))) else (if x<3238 then (if x<3180 then 2 else (if x<3222 then 1 else 3)) else (if x<3274 then 2 else (if x<3276 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5702 : Finset ℕ := ([1652,1714,1720,1748,1752,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5702 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5702 1720 4
  · have he : independentCachedBranchMembers5702.erase 1720=independentCachedBranchMembers5700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5700
  · have he : independentCachedBranchMembers5702.filter (independentCachedEdge 1720)=independentCachedBranchMembers5701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5701
def independentCachedBranchMembers5703 : Finset ℕ := ([1652,1714,3072,3132,3164,3180,3222,3226,3238,3242,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5703 4 (fun x => (if x<3222 then (if x<3132 then (if x<1714 then 0 else (if x<3072 then 0 else 1)) else (if x<3164 then 1 else (if x<3180 then 0 else 2))) else (if x<3242 then (if x<3226 then 1 else (if x<3238 then 0 else 2)) else (if x<3270 then 1 else (if x<3274 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5704 : Finset ℕ := ([1650,1652,1714,1720,1748,1752,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3222,3226,3228,3238,3242,3244,3270,3274,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5704 1650 4
  · have he : independentCachedBranchMembers5704.erase 1650=independentCachedBranchMembers5702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5702
  · have he : independentCachedBranchMembers5704.filter (independentCachedEdge 1650)=independentCachedBranchMembers5703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5703
def independentCachedBranchMembers5705 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,1776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5705 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5705 1776 5
  · have he : independentCachedBranchMembers5705.erase 1776=independentCachedBranchMembers5697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5697
  · have he : independentCachedBranchMembers5705.filter (independentCachedEdge 1776)=independentCachedBranchMembers5704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5704
def independentCachedBranchMembers5706 : Finset ℕ := ([1644,1702,1714,1734,1748,3072,3118,3130,3132,3150,3162,3164,3174,3186,3188,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5706 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5706 5 (fun x => (if x<3174 then (if x<3118 then (if x<1734 then (if x<1702 then 0 else (if x<1714 then 0 else 1)) else (if x<1748 then 1 else (if x<3072 then 0 else 2))) else (if x<3150 then (if x<3130 then 0 else (if x<3132 then 1 else 2)) else (if x<3162 then 1 else (if x<3164 then 2 else 0)))) else (if x<3256 then (if x<3222 then (if x<3186 then 2 else (if x<3188 then 3 else 4)) else (if x<3242 then 0 else (if x<3244 then 2 else 4))) else (if x<3288 then (if x<3274 then 3 else (if x<3276 then 3 else 2)) else (if x<3300 then (if x<3298 then 4 else 1) else (if x<3312 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5707 : Finset ℕ := ([1644,1748,3072,3132,3164,3188,3244,3256,3276,3288,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5707 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5707 4 (fun x => (if x<3244 then (if x<3132 then (if x<1748 then 0 else (if x<3072 then 0 else 1)) else (if x<3164 then 1 else (if x<3188 then 0 else 2))) else (if x<3288 then (if x<3256 then 2 else (if x<3276 then 3 else 1)) else (if x<3300 then 2 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5708 : Finset ℕ := ([1642,1644,1702,1714,1734,1748,3072,3118,3130,3132,3150,3162,3164,3174,3186,3188,3222,3242,3244,3256,3274,3276,3288,3298,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5708 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5708 1642 4
  · have he : independentCachedBranchMembers5708.erase 1642=independentCachedBranchMembers5706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5706
  · have he : independentCachedBranchMembers5708.filter (independentCachedEdge 1642)=independentCachedBranchMembers5707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5707
def independentCachedBranchMembers5709 : Finset ℕ := ([1642,1644,1650,1652,1686,1702,1708,1714,1720,1734,1738,1748,1752,1776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5709 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5709 1686 5
  · have he : independentCachedBranchMembers5709.erase 1686=independentCachedBranchMembers5705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5705
  · have he : independentCachedBranchMembers5709.filter (independentCachedEdge 1686)=independentCachedBranchMembers5708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5708
def independentCachedBranchMembers5710 : Finset ℕ := ([1650,1702,1708,1738,1752,3072,3118,3126,3132,3162,3174,3180,3188,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5710 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5710 5 (fun x => (if x<3188 then (if x<3118 then (if x<1738 then (if x<1702 then 0 else (if x<1708 then 0 else 1)) else (if x<1752 then 0 else (if x<3072 then 1 else 2))) else (if x<3162 then (if x<3126 then 1 else (if x<3132 then 0 else 2)) else (if x<3174 then 0 else (if x<3180 then 2 else 3)))) else (if x<3256 then (if x<3228 then (if x<3214 then 4 else (if x<3222 then 0 else 2)) else (if x<3242 then 1 else (if x<3250 then 2 else 4))) else (if x<3284 then (if x<3270 then 3 else (if x<3276 then 4 else 2)) else (if x<3304 then (if x<3298 then 3 else 0) else (if x<3312 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5711 : Finset ℕ := ([1650,1738,3072,3126,3132,3188,3214,3250,3256,3270,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5711 4 (fun x => (if x<3214 then (if x<3126 then (if x<1738 then 0 else (if x<3072 then 0 else 1)) else (if x<3132 then 0 else (if x<3188 then 1 else 2))) else (if x<3270 then (if x<3250 then 0 else (if x<3256 then 1 else 2)) else (if x<3276 then 3 else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5712 : Finset ℕ := ([1642,1650,1702,1708,1738,1752,3072,3118,3126,3132,3162,3174,3180,3188,3214,3222,3228,3242,3250,3256,3270,3276,3284,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5712 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5712 1642 4
  · have he : independentCachedBranchMembers5712.erase 1642=independentCachedBranchMembers5710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5710
  · have he : independentCachedBranchMembers5712.filter (independentCachedEdge 1642)=independentCachedBranchMembers5711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5711
def independentCachedBranchMembers5713 : Finset ℕ := ([1626,1642,1644,1650,1652,1686,1702,1708,1714,1720,1734,1738,1748,1752,1776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5713 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5713 1626 5
  · have he : independentCachedBranchMembers5713.erase 1626=independentCachedBranchMembers5709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5709
  · have he : independentCachedBranchMembers5713.filter (independentCachedEdge 1626)=independentCachedBranchMembers5712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5712
def independentCachedBranchMembers5714 : Finset ℕ := ([1652,1708,1734,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5714 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5714 5 (fun x => (if x<3214 then (if x<3150 then (if x<1734 then (if x<1708 then 0 else 0) else (if x<3072 then 0 else (if x<3132 then 1 else 0))) else (if x<3174 then (if x<3158 then 1 else (if x<3162 then 0 else 2)) else (if x<3178 then 2 else (if x<3186 then 3 else 1)))) else (if x<3276 then (if x<3238 then (if x<3222 then 0 else (if x<3226 then 1 else 3)) else (if x<3242 then 3 else (if x<3250 then 1 else 2))) else (if x<3300 then (if x<3284 then 3 else (if x<3288 then 2 else 1)) else (if x<3304 then 0 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5715 : Finset ℕ := ([1652,1734,3072,3158,3174,3186,3222,3238,3250,3284,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5715 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5715 4 (fun x => (if x<3222 then (if x<3158 then (if x<1734 then 0 else (if x<3072 then 0 else 1)) else (if x<3174 then 0 else (if x<3186 then 1 else 2))) else (if x<3284 then (if x<3238 then 1 else (if x<3250 then 2 else 3)) else (if x<3300 then 2 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5716 : Finset ℕ := ([1652,1708,1734,1738,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5716 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5716 1738 4
  · have he : independentCachedBranchMembers5716.erase 1738=independentCachedBranchMembers5714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5714
  · have he : independentCachedBranchMembers5716.filter (independentCachedEdge 1738)=independentCachedBranchMembers5715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5715
def independentCachedBranchMembers5717 : Finset ℕ := ([1708,1734,3072,3162,3178,3186,3214,3222,3238,3276,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5717 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5717 4 (fun x => (if x<3214 then (if x<3162 then (if x<1734 then 0 else (if x<3072 then 0 else 1)) else (if x<3178 then 1 else (if x<3186 then 2 else 3))) else (if x<3276 then (if x<3222 then 0 else (if x<3238 then 1 else 2)) else (if x<3284 then 1 else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5718 : Finset ℕ := ([1652,1708,1720,1734,1738,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5718 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5718 1720 4
  · have he : independentCachedBranchMembers5718.erase 1720=independentCachedBranchMembers5716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5716
  · have he : independentCachedBranchMembers5718.filter (independentCachedEdge 1720)=independentCachedBranchMembers5717 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5717
def independentCachedBranchMembers5719 : Finset ℕ := ([1652,1708,3072,3158,3162,3186,3214,3238,3242,3284,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5719 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5719 4 (fun x => (if x<3214 then (if x<3158 then (if x<1708 then 0 else (if x<3072 then 0 else 1)) else (if x<3162 then 0 else (if x<3186 then 1 else 2))) else (if x<3284 then (if x<3238 then 0 else (if x<3242 then 2 else 1)) else (if x<3288 then 2 else (if x<3312 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5720 : Finset ℕ := ([1644,1652,1708,1720,1734,1738,3072,3132,3150,3158,3162,3174,3178,3186,3214,3222,3226,3238,3242,3250,3276,3284,3288,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5720 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5720 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5720 1644 4
  · have he : independentCachedBranchMembers5720.erase 1644=independentCachedBranchMembers5718 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5718
  · have he : independentCachedBranchMembers5720.filter (independentCachedEdge 1644)=independentCachedBranchMembers5719 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5719
def independentCachedBranchMembers5721 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1708,1714,1720,1734,1738,1748,1752,1776,3072,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5721 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5721 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5721 1596 5
  · have he : independentCachedBranchMembers5721.erase 1596=independentCachedBranchMembers5713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5713
  · have he : independentCachedBranchMembers5721.filter (independentCachedEdge 1596)=independentCachedBranchMembers5720 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5720
def independentCachedBranchMembers5722 : Finset ℕ := ([1708,1714,1738,1748,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5722 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5722 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5722 5 (fun x => (if x<3162 then (if x<3126 then (if x<1738 then (if x<1714 then 0 else 0) else (if x<1748 then 0 else (if x<3118 then 0 else 1))) else (if x<3132 then (if x<3130 then 2 else 3) else (if x<3150 then 4 else (if x<3158 then 2 else 1)))) else (if x<3228 then (if x<3214 then (if x<3164 then 4 else 3) else (if x<3222 then 3 else (if x<3226 then 4 else 1))) else (if x<3300 then (if x<3298 then 2 else 1) else (if x<3304 then 2 else (if x<3312 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5723 : Finset ℕ := ([1738,1748,3130,3132,3150,3158,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5723 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5723 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5723 4 (fun x => (if x<3158 then (if x<3130 then (if x<1748 then 0 else 0) else (if x<3132 then 1 else (if x<3150 then 2 else 1))) else (if x<3222 then (if x<3214 then 2 else 2) else (if x<3298 then 1 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5724 : Finset ℕ := ([1708,1714,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5724 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5724 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5724 1752 4
  · have he : independentCachedBranchMembers5724.erase 1752=independentCachedBranchMembers5722 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5722
  · have he : independentCachedBranchMembers5724.filter (independentCachedEdge 1752)=independentCachedBranchMembers5723 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5723
def independentCachedBranchMembers5725 : Finset ℕ := ([1738,1748,3118,3126,3162,3164,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5725 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5725 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5725 4 (fun x => (if x<3164 then (if x<3118 then (if x<1748 then 0 else 0) else (if x<3126 then 1 else (if x<3162 then 2 else 1))) else (if x<3228 then (if x<3226 then 2 else 2) else (if x<3304 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5726 : Finset ℕ := ([1708,1714,1734,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5726 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5726 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5726 1734 4
  · have he : independentCachedBranchMembers5726.erase 1734=independentCachedBranchMembers5724 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5724
  · have he : independentCachedBranchMembers5726.filter (independentCachedEdge 1734)=independentCachedBranchMembers5725 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5725
def independentCachedBranchMembers5727 : Finset ℕ := ([1708,1714,3118,3132,3150,3164,3222,3226,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5727 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5727 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5727 4 (fun x => (if x<3164 then (if x<3118 then (if x<1714 then 0 else 0) else (if x<3132 then 1 else (if x<3150 then 2 else 2))) else (if x<3226 then (if x<3222 then 1 else 1) else (if x<3300 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
