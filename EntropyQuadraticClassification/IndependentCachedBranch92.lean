/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch91
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5728 : Finset ℕ := ([1650,1708,1714,1734,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5728 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5728 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5728 1650 4
  · have he : independentCachedBranchMembers5728.erase 1650=independentCachedBranchMembers5726 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5726
  · have he : independentCachedBranchMembers5728.filter (independentCachedEdge 1650)=independentCachedBranchMembers5727 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5727
def independentCachedBranchMembers5729 : Finset ℕ := ([1708,1714,3126,3130,3158,3162,3214,3228,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5729 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5729 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5729 4 (fun x => (if x<3162 then (if x<3126 then (if x<1714 then 0 else 0) else (if x<3130 then 1 else (if x<3158 then 2 else 2))) else (if x<3228 then (if x<3214 then 1 else 1) else (if x<3298 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5730 : Finset ℕ := ([1644,1650,1708,1714,1734,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5730 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5730 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5730 1644 4
  · have he : independentCachedBranchMembers5730.erase 1644=independentCachedBranchMembers5728 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5728
  · have he : independentCachedBranchMembers5730.filter (independentCachedEdge 1644)=independentCachedBranchMembers5729 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5729
def independentCachedBranchMembers5731 : Finset ℕ := ([1708,1714,1734,1752,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5731 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5731 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5731 4 (fun x => (if x<3162 then (if x<1752 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<3118 then 0 else (if x<3126 then 1 else 2))) else (if x<3222 then (if x<3164 then 1 else (if x<3214 then 2 else 2)) else (if x<3298 then 1 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5732 : Finset ℕ := ([1644,1650,1708,1714,1720,1734,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5732 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5732 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5732 1720 4
  · have he : independentCachedBranchMembers5732.erase 1720=independentCachedBranchMembers5730 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5730
  · have he : independentCachedBranchMembers5732.filter (independentCachedEdge 1720)=independentCachedBranchMembers5731 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5731
def independentCachedBranchMembers5733 : Finset ℕ := ([1708,1714,1734,1752,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5733 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5733 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5733 4 (fun x => (if x<3150 then (if x<1752 then (if x<1714 then 0 else (if x<1734 then 0 else 0)) else (if x<3130 then 0 else (if x<3132 then 1 else 2))) else (if x<3228 then (if x<3158 then 1 else (if x<3226 then 2 else 2)) else (if x<3304 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5734 : Finset ℕ := ([1644,1650,1702,1708,1714,1720,1734,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5734 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5734 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5734 1702 4
  · have he : independentCachedBranchMembers5734.erase 1702=independentCachedBranchMembers5732 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5732
  · have he : independentCachedBranchMembers5734.filter (independentCachedEdge 1702)=independentCachedBranchMembers5733 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5733
def independentCachedBranchMembers5735 : Finset ℕ := ([1644,1650,1738,1748,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5735 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5735 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5735 4 (fun x => (if x<3150 then (if x<1748 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<3118 then 0 else (if x<3130 then 1 else 2))) else (if x<3228 then (if x<3162 then 2 else (if x<3222 then 1 else 1)) else (if x<3298 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5736 : Finset ℕ := ([1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5736 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5736 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5736 1652 4
  · have he : independentCachedBranchMembers5736.erase 1652=independentCachedBranchMembers5734 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5734
  · have he : independentCachedBranchMembers5736.filter (independentCachedEdge 1652)=independentCachedBranchMembers5735 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5735
def independentCachedBranchMembers5737 : Finset ℕ := ([1644,1650,1738,1748,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5737 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5737 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5737 4 (fun x => (if x<3158 then (if x<1748 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<3126 then 0 else (if x<3132 then 1 else 2))) else (if x<3226 then (if x<3164 then 2 else (if x<3214 then 1 else 1)) else (if x<3300 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5738 : Finset ℕ := ([1642,1644,1650,1652,1702,1708,1714,1720,1734,1738,1748,1752,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5738 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5738 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5738 1642 4
  · have he : independentCachedBranchMembers5738.erase 1642=independentCachedBranchMembers5736 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5736
  · have he : independentCachedBranchMembers5738.filter (independentCachedEdge 1642)=independentCachedBranchMembers5737 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5737
def independentCachedBranchMembers5739 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1708,1714,1720,1734,1738,1748,1752,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5739 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5739 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5739 3102 5
  · have he : independentCachedBranchMembers5739.erase 3102=independentCachedBranchMembers5721 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5721
  · have he : independentCachedBranchMembers5739.filter (independentCachedEdge 3102)=independentCachedBranchMembers5738 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5738
def independentCachedBranchMembers5740 : Finset ℕ := ([1644,1686,1708,1720,1738,1752,1776,3072,3118,3132,3150,3162,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5740 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5740 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5740 5 (fun x => (if x<3174 then (if x<1776 then (if x<1720 then (if x<1686 then 0 else (if x<1708 then 1 else 1)) else (if x<1738 then 0 else (if x<1752 then 0 else 1))) else (if x<3132 then (if x<3072 then 2 else (if x<3118 then 3 else 2)) else (if x<3150 then 0 else (if x<3162 then 0 else 3)))) else (if x<3238 then (if x<3214 then (if x<3186 then 3 else (if x<3188 then 2 else 4)) else (if x<3226 then 3 else (if x<3228 then 0 else 1))) else (if x<3270 then (if x<3250 then 1 else (if x<3252 then 3 else 2)) else (if x<3284 then (if x<3282 then 4 else 1) else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5741 : Finset ℕ := ([1644,1686,1738,3072,3132,3188,3214,3226,3238,3250,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5741 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5741 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5741 4 (fun x => (if x<3214 then (if x<3072 then (if x<1686 then 0 else (if x<1738 then 1 else 0)) else (if x<3132 then 2 else (if x<3188 then 0 else 2))) else (if x<3250 then (if x<3226 then 1 else (if x<3238 then 0 else 2)) else (if x<3270 then 1 else (if x<3282 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5742 : Finset ℕ := ([1642,1644,1686,1708,1720,1738,1752,1776,3072,3118,3132,3150,3162,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5742 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5742 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5742 1642 4
  · have he : independentCachedBranchMembers5742.erase 1642=independentCachedBranchMembers5740 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5740
  · have he : independentCachedBranchMembers5742.filter (independentCachedEdge 1642)=independentCachedBranchMembers5741 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5741
def independentCachedBranchMembers5743 : Finset ℕ := ([1642,1686,1708,1720,1738,1776,3132,3150,3162,3188,3228,3238,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5743 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5743 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5743 4 (fun x => (if x<3150 then (if x<1720 then (if x<1686 then 0 else (if x<1708 then 1 else 0)) else (if x<1776 then (if x<1738 then 1 else 1) else (if x<3132 then 0 else 2))) else (if x<3228 then (if x<3162 then 2 else (if x<3188 then 3 else 3)) else (if x<3250 then (if x<3238 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5744 : Finset ℕ := ([1642,1644,1686,1708,1720,1738,1752,1776,3072,3118,3132,3150,3162,3164,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5744 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5744 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5744 3164 4
  · have he : independentCachedBranchMembers5744.erase 3164=independentCachedBranchMembers5742 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5742
  · have he : independentCachedBranchMembers5744.filter (independentCachedEdge 3164)=independentCachedBranchMembers5743 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5743
def independentCachedBranchMembers5745 : Finset ℕ := ([1644,1686,1708,1738,1752,1776,3118,3132,3162,3186,3226,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound5745 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5745 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5745 4 (fun x => (if x<3132 then (if x<1738 then (if x<1686 then 0 else (if x<1708 then 1 else 1)) else (if x<1776 then (if x<1752 then 0 else 1) else (if x<3118 then 0 else 2))) else (if x<3226 then (if x<3162 then 3 else (if x<3186 then 2 else 3)) else (if x<3270 then (if x<3250 then 3 else 2) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5746 : Finset ℕ := ([1642,1644,1686,1708,1720,1738,1752,1776,3072,3118,3130,3132,3150,3162,3164,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5746 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5746 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5746 3130 4
  · have he : independentCachedBranchMembers5746.erase 3130=independentCachedBranchMembers5744 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5744
  · have he : independentCachedBranchMembers5746.filter (independentCachedEdge 3130)=independentCachedBranchMembers5745 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5745
def independentCachedBranchMembers5747 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1686,1702,1708,1714,1720,1734,1738,1748,1752,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5747 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5747 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5747 1768 5
  · have he : independentCachedBranchMembers5747.erase 1768=independentCachedBranchMembers5739 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5739
  · have he : independentCachedBranchMembers5747.filter (independentCachedEdge 1768)=independentCachedBranchMembers5746 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5746
def independentCachedBranchMembers5748 : Finset ℕ := ([1650,1652,1686,1702,1708,1734,1738,1776,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5748 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5748 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5748 5 (fun x => (if x<3164 then (if x<1776 then (if x<1702 then (if x<1652 then 0 else (if x<1686 then 1 else 0)) else (if x<1734 then (if x<1708 then 1 else 2) else (if x<1738 then 2 else 0))) else (if x<3130 then (if x<3072 then 2 else (if x<3126 then 3 else 0)) else (if x<3158 then (if x<3132 then 3 else 4) else (if x<3162 then 3 else 4)))) else (if x<3256 then (if x<3180 then (if x<3174 then 1 else (if x<3178 then 1 else 0)) else (if x<3250 then (if x<3214 then 3 else 0) else (if x<3252 then 4 else 1))) else (if x<3288 then (if x<3282 then 2 else (if x<3284 then 0 else 4)) else (if x<3300 then (if x<3298 then 3 else 3) else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5749 : Finset ℕ := ([1596,1626,1642,1644,1650,1652,1678,1686,1702,1708,1714,1720,1734,1738,1748,1752,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5749 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5749 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5749 1678 5
  · have he : independentCachedBranchMembers5749.erase 1678=independentCachedBranchMembers5747 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5747
  · have he : independentCachedBranchMembers5749.filter (independentCachedEdge 1678)=independentCachedBranchMembers5748 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5748
def independentCachedBranchMembers5750 : Finset ℕ := ([1596,1626,1652,1714,1748,1752,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5750 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5750 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5750 5 (fun x => (if x<3178 then (if x<3072 then (if x<1714 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<1748 then 0 else (if x<1752 then 0 else 1))) else (if x<3130 then (if x<3118 then 2 else (if x<3126 then 2 else 1)) else (if x<3164 then 0 else (if x<3174 then 0 else 3)))) else (if x<3256 then (if x<3226 then (if x<3186 then 4 else (if x<3222 then 2 else 2)) else (if x<3244 then 1 else (if x<3252 then 3 else 0))) else (if x<3282 then (if x<3270 then 2 else (if x<3274 then 4 else 2)) else (if x<3300 then 0 else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5751 : Finset ℕ := ([1626,1714,1752,3072,3130,3178,3186,3226,3256,3274,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5751 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5751 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5751 4 (fun x => (if x<3186 then (if x<3072 then (if x<1714 then 0 else (if x<1752 then 0 else 1)) else (if x<3130 then 2 else (if x<3178 then 0 else 2))) else (if x<3274 then (if x<3226 then 3 else (if x<3256 then 1 else 2)) else (if x<3282 then 3 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5752 : Finset ℕ := ([1596,1626,1652,1702,1714,1748,1752,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5752 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5752 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5752 1702 4
  · have he : independentCachedBranchMembers5752.erase 1702=independentCachedBranchMembers5750 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5750
  · have he : independentCachedBranchMembers5752.filter (independentCachedEdge 1702)=independentCachedBranchMembers5751 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5751
def independentCachedBranchMembers5753 : Finset ℕ := ([1596,1652,1714,3072,3126,3130,3186,3252,3256,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5753 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5753 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5753 4 (fun x => (if x<3186 then (if x<3072 then (if x<1652 then 0 else (if x<1714 then 1 else 0)) else (if x<3126 then 2 else (if x<3130 then 0 else 2))) else (if x<3270 then (if x<3252 then 1 else (if x<3256 then 1 else 0)) else (if x<3274 then 3 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5754 : Finset ℕ := ([1596,1626,1644,1652,1702,1714,1748,1752,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5754 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5754 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5754 1644 4
  · have he : independentCachedBranchMembers5754.erase 1644=independentCachedBranchMembers5752 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5752
  · have he : independentCachedBranchMembers5754.filter (independentCachedEdge 1644)=independentCachedBranchMembers5753 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5753
def independentCachedBranchMembers5755 : Finset ℕ := ([1596,1626,1652,1702,1714,1748,3126,3178,3222,3244,3256,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5755 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5755 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5755 4 (fun x => (if x<3178 then (if x<1702 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<1748 then (if x<1714 then 1 else 0) else (if x<3126 then 0 else 1))) else (if x<3256 then (if x<3222 then 2 else (if x<3244 then 3 else 2)) else (if x<3300 then (if x<3274 then 3 else 3) else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5756 : Finset ℕ := ([1596,1626,1644,1652,1702,1714,1748,1752,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5756 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5756 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5756 3304 4
  · have he : independentCachedBranchMembers5756.erase 3304=independentCachedBranchMembers5754 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5754
  · have he : independentCachedBranchMembers5756.filter (independentCachedEdge 3304)=independentCachedBranchMembers5755 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5755
def independentCachedBranchMembers5757 : Finset ℕ := ([1596,1626,1644,1714,1748,1752,3118,3186,3222,3226,3244,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5757 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5757 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5757 4 (fun x => (if x<3186 then (if x<1714 then (if x<1626 then 0 else (if x<1644 then 0 else 1)) else (if x<1752 then (if x<1748 then 0 else 0) else (if x<3118 then 1 else 1))) else (if x<3244 then (if x<3222 then 2 else (if x<3226 then 2 else 1)) else (if x<3274 then (if x<3270 then 3 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5758 : Finset ℕ := ([1596,1626,1644,1652,1702,1714,1748,1752,3072,3118,3126,3130,3164,3174,3178,3186,3214,3222,3226,3244,3252,3256,3270,3274,3282,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5758 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5758 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5758 3214 4
  · have he : independentCachedBranchMembers5758.erase 3214=independentCachedBranchMembers5756 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5756
  · have he : independentCachedBranchMembers5758.filter (independentCachedEdge 3214)=independentCachedBranchMembers5757 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5757
def independentCachedBranchMembers5759 : Finset ℕ := ([1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1708,1714,1720,1734,1738,1748,1752,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5759 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5759 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5759 1628 5
  · have he : independentCachedBranchMembers5759.erase 1628=independentCachedBranchMembers5749 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5749
  · have he : independentCachedBranchMembers5759.filter (independentCachedEdge 1628)=independentCachedBranchMembers5758 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5758
end EntropyDesigns.QuadraticRefinement
