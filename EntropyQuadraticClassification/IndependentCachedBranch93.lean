/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch92
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5760 : Finset ℕ := ([1596,1626,1650,1714,1734,1748,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5760 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5760 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5760 5 (fun x => (if x<3180 then (if x<3072 then (if x<1714 then (if x<1626 then 0 else (if x<1650 then 0 else 1)) else (if x<1734 then 0 else (if x<1748 then 1 else 0))) else (if x<3158 then (if x<3130 then 2 else (if x<3150 then 0 else 2)) else (if x<3164 then 1 else (if x<3174 then 0 else 3)))) else (if x<3252 then (if x<3228 then (if x<3188 then 4 else (if x<3222 then 2 else 2)) else (if x<3238 then 4 else (if x<3244 then 4 else 2))) else (if x<3288 then (if x<3274 then 0 else (if x<3282 then 3 else 0)) else (if x<3298 then 2 else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5761 : Finset ℕ := ([1596,1714,1734,3072,3164,3180,3188,3222,3238,3274,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5761 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5761 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5761 4 (fun x => (if x<3188 then (if x<3072 then (if x<1714 then 0 else (if x<1734 then 0 else 1)) else (if x<3164 then 2 else (if x<3180 then 0 else 2))) else (if x<3274 then (if x<3222 then 3 else (if x<3238 then 1 else 2)) else (if x<3282 then 1 else (if x<3298 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5762 : Finset ℕ := ([1596,1626,1650,1714,1720,1734,1748,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5762 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5762 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5762 1720 4
  · have he : independentCachedBranchMembers5762.erase 1720=independentCachedBranchMembers5760 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5760
  · have he : independentCachedBranchMembers5762.filter (independentCachedEdge 1720)=independentCachedBranchMembers5761 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5761
def independentCachedBranchMembers5763 : Finset ℕ := ([1626,1650,1748,3072,3158,3164,3188,3238,3244,3282,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5763 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5763 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5763 4 (fun x => (if x<3188 then (if x<3072 then (if x<1650 then 0 else (if x<1748 then 1 else 0)) else (if x<3158 then 2 else (if x<3164 then 0 else 2))) else (if x<3282 then (if x<3238 then 1 else (if x<3244 then 3 else 1)) else (if x<3288 then 2 else (if x<3312 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5764 : Finset ℕ := ([1596,1626,1642,1650,1714,1720,1734,1748,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5764 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5764 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5764 1642 4
  · have he : independentCachedBranchMembers5764.erase 1642=independentCachedBranchMembers5762 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5762
  · have he : independentCachedBranchMembers5764.filter (independentCachedEdge 1642)=independentCachedBranchMembers5763 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5763
def independentCachedBranchMembers5765 : Finset ℕ := ([1596,1626,1650,1714,1734,1748,3158,3180,3222,3244,3274,3288,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5765 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5765 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5765 4 (fun x => (if x<3180 then (if x<1714 then (if x<1626 then 0 else (if x<1650 then 0 else 1)) else (if x<1748 then (if x<1734 then 0 else 1) else (if x<3158 then 0 else 1))) else (if x<3274 then (if x<3222 then 2 else (if x<3244 then 3 else 3)) else (if x<3298 then (if x<3288 then 2 else 3) else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5766 : Finset ℕ := ([1596,1626,1642,1650,1714,1720,1734,1748,3072,3130,3150,3158,3164,3174,3180,3188,3222,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5766 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5766 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5766 3304 4
  · have he : independentCachedBranchMembers5766.erase 3304=independentCachedBranchMembers5764 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5764
  · have he : independentCachedBranchMembers5766.filter (independentCachedEdge 3304)=independentCachedBranchMembers5765 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5765
def independentCachedBranchMembers5767 : Finset ℕ := ([1596,1626,1642,1714,1720,1748,3150,3188,3222,3228,3238,3244,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5767 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5767 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5767 4 (fun x => (if x<3188 then (if x<1714 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1748 then (if x<1720 then 0 else 1) else (if x<3150 then 0 else 1))) else (if x<3238 then (if x<3222 then 2 else (if x<3228 then 2 else 1)) else (if x<3274 then (if x<3244 then 3 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5768 : Finset ℕ := ([1596,1626,1642,1650,1714,1720,1734,1748,3072,3130,3150,3158,3164,3174,3180,3188,3214,3222,3228,3238,3244,3252,3274,3282,3288,3298,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5768 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5768 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5768 3214 4
  · have he : independentCachedBranchMembers5768.erase 3214=independentCachedBranchMembers5766 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5766
  · have he : independentCachedBranchMembers5768.filter (independentCachedEdge 3214)=independentCachedBranchMembers5767 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5767
def independentCachedBranchMembers5769 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1708,1714,1720,1734,1738,1748,1752,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5769 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5769 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5769 1594 5
  · have he : independentCachedBranchMembers5769.erase 1594=independentCachedBranchMembers5759 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5759
  · have he : independentCachedBranchMembers5769.filter (independentCachedEdge 1594)=independentCachedBranchMembers5768 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5768
def independentCachedBranchMembers5770 : Finset ℕ := ([1594,1626,1644,1652,1702,1734,1768,1776,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5770 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5770 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5770 5 (fun x => (if x<3158 then (if x<1768 then (if x<1652 then (if x<1626 then 0 else (if x<1644 then 1 else 0)) else (if x<1702 then 1 else (if x<1734 then 0 else 1))) else (if x<3118 then (if x<1776 then 1 else (if x<3072 then 0 else 2)) else (if x<3132 then (if x<3126 then 0 else 2) else (if x<3150 then 3 else 2)))) else (if x<3242 then (if x<3186 then (if x<3164 then 1 else (if x<3178 then 4 else 3)) else (if x<3214 then (if x<3192 then 4 else 0) else (if x<3222 then 3 else 4))) else (if x<3274 then (if x<3250 then 2 else (if x<3256 then 0 else 4)) else (if x<3288 then (if x<3282 then 1 else 2) else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5771 : Finset ℕ := ([1594,1652,1734,1776,3072,3132,3150,3186,3192,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5771 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5771 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5771 4 (fun x => (if x<3150 then (if x<1776 then (if x<1652 then 0 else (if x<1734 then 0 else 1)) else (if x<3072 then 1 else (if x<3132 then 2 else 0))) else (if x<3214 then (if x<3186 then 1 else (if x<3192 then 0 else 1)) else (if x<3256 then (if x<3250 then 2 else 2) else (if x<3274 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5772 : Finset ℕ := ([1734,1776,3132,3186,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5772 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5772 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5772 3 (fun x => (if x<3186 then (if x<1776 then 0 else (if x<3132 then 0 else 1)) else (if x<3250 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5773 : Finset ℕ := ([1594,1652,1734,1776,3072,3126,3132,3150,3186,3192,3214,3250,3256,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5773 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5773 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5773 3126 3
  · have he : independentCachedBranchMembers5773.erase 3126=independentCachedBranchMembers5771 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5771
  · have he : independentCachedBranchMembers5773.filter (independentCachedEdge 3126)=independentCachedBranchMembers5772 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5772
def independentCachedBranchMembers5774 : Finset ℕ := ([1594,1626,1644,1652,1702,1734,1748,1768,1776,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5774 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5774 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5774 1748 4
  · have he : independentCachedBranchMembers5774.erase 1748=independentCachedBranchMembers5770 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5770
  · have he : independentCachedBranchMembers5774.filter (independentCachedEdge 1748)=independentCachedBranchMembers5773 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5773
def independentCachedBranchMembers5775 : Finset ℕ := ([1626,1644,1702,1768,3072,3150,3164,3178,3192,3222,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5775 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5775 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5775 4 (fun x => (if x<3164 then (if x<1768 then (if x<1644 then 0 else (if x<1702 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3222 then (if x<3178 then 2 else (if x<3192 then 2 else 0)) else (if x<3274 then (if x<3250 then 1 else 3) else (if x<3288 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5776 : Finset ℕ := ([1626,1644,3222,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5776 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5776 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5776 3 (fun x => (if x<3250 then (if x<1644 then 0 else (if x<3222 then 0 else 1)) else (if x<3274 then 2 else (if x<3288 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5777 : Finset ℕ := ([1626,1644,1702,1768,3072,3126,3150,3164,3178,3192,3222,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5777 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5777 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5777 3126 3
  · have he : independentCachedBranchMembers5777.erase 3126=independentCachedBranchMembers5775 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5775
  · have he : independentCachedBranchMembers5777.filter (independentCachedEdge 3126)=independentCachedBranchMembers5776 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5776
def independentCachedBranchMembers5778 : Finset ℕ := ([1594,1626,1644,1652,1702,1708,1734,1748,1768,1776,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5778 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5778 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5778 1708 4
  · have he : independentCachedBranchMembers5778.erase 1708=independentCachedBranchMembers5774 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5774
  · have he : independentCachedBranchMembers5778.filter (independentCachedEdge 1708)=independentCachedBranchMembers5777 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5777
def independentCachedBranchMembers5779 : Finset ℕ := ([1594,1626,1644,1652,1702,1734,1768,1776,3132,3164,3178,3186,3214,3222,3256,3288] : List ℕ).toFinset
theorem independentCachedBranchBound5779 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5779 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5779 4 (fun x => (if x<3132 then (if x<1702 then (if x<1644 then (if x<1626 then 0 else 1) else (if x<1652 then 0 else 1)) else (if x<1768 then (if x<1734 then 0 else 1) else (if x<1776 then 1 else 0))) else (if x<3214 then (if x<3178 then (if x<3164 then 2 else 3) else (if x<3186 then 2 else 3)) else (if x<3256 then (if x<3222 then 2 else 3) else (if x<3288 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5780 : Finset ℕ := ([1594,1626,1644,1652,1702,1708,1734,1748,1768,1776,3072,3118,3126,3132,3150,3158,3164,3178,3186,3192,3214,3222,3228,3242,3250,3256,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound5780 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5780 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5780 3228 4
  · have he : independentCachedBranchMembers5780.erase 3228=independentCachedBranchMembers5778 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5778
  · have he : independentCachedBranchMembers5780.filter (independentCachedEdge 3228)=independentCachedBranchMembers5779 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5779
def independentCachedBranchMembers5781 : Finset ℕ := ([1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1708,1714,1720,1734,1738,1748,1752,1764,1768,1776,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5781 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5781 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5781 1764 5
  · have he : independentCachedBranchMembers5781.erase 1764=independentCachedBranchMembers5769 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5769
  · have he : independentCachedBranchMembers5781.filter (independentCachedEdge 1764)=independentCachedBranchMembers5780 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5780
def independentCachedBranchMembers5782 : Finset ℕ := ([1596,1628,1642,1650,1678,1686,1720,1752,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5782 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5782 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5782 5 (fun x => (if x<3158 then (if x<1720 then (if x<1650 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<1678 then 1 else (if x<1686 then 0 else 1))) else (if x<3118 then (if x<1752 then 1 else (if x<3072 then 0 else 2)) else (if x<3130 then (if x<3126 then 0 else 2) else (if x<3150 then 3 else 2)))) else (if x<3242 then (if x<3188 then (if x<3162 then 1 else (if x<3180 then 4 else 3)) else (if x<3228 then (if x<3192 then 4 else 0) else (if x<3238 then 0 else 3))) else (if x<3274 then (if x<3250 then 2 else (if x<3270 then 1 else 4)) else (if x<3304 then (if x<3282 then 0 else 2) else (if x<3312 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5783 : Finset ℕ := ([1628,1642,1686,1752,3072,3150,3162,3180,3192,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5783 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5783 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5783 4 (fun x => (if x<3162 then (if x<1752 then (if x<1642 then 0 else (if x<1686 then 0 else 1)) else (if x<3072 then 1 else (if x<3150 then 2 else 0))) else (if x<3238 then (if x<3180 then 2 else (if x<3192 then 2 else 0)) else (if x<3274 then (if x<3250 then 1 else 3) else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5784 : Finset ℕ := ([1628,1642,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5784 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5784 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5784 3 (fun x => (if x<3250 then (if x<1642 then 0 else (if x<3238 then 0 else 1)) else (if x<3274 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5785 : Finset ℕ := ([1628,1642,1686,1752,3072,3126,3150,3162,3180,3192,3238,3250,3274,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5785 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5785 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5785 3126 3
  · have he : independentCachedBranchMembers5785.erase 3126=independentCachedBranchMembers5783 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5783
  · have he : independentCachedBranchMembers5785.filter (independentCachedEdge 3126)=independentCachedBranchMembers5784 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5784
def independentCachedBranchMembers5786 : Finset ℕ := ([1596,1628,1642,1650,1678,1686,1720,1748,1752,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5786 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5786 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5786 1748 4
  · have he : independentCachedBranchMembers5786.erase 1748=independentCachedBranchMembers5782 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5782
  · have he : independentCachedBranchMembers5786.filter (independentCachedEdge 1748)=independentCachedBranchMembers5785 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5785
def independentCachedBranchMembers5787 : Finset ℕ := ([1596,1650,1678,1720,3072,3130,3150,3188,3192,3250,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5787 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5787 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5787 4 (fun x => (if x<3150 then (if x<1720 then (if x<1650 then 0 else (if x<1678 then 0 else 1)) else (if x<3072 then 1 else (if x<3130 then 2 else 0))) else (if x<3250 then (if x<3188 then 1 else (if x<3192 then 0 else 1)) else (if x<3274 then (if x<3270 then 2 else 2) else (if x<3312 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5788 : Finset ℕ := ([1678,1720,3130,3188,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound5788 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5788 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5788 3 (fun x => (if x<3188 then (if x<1720 then 0 else (if x<3130 then 0 else 1)) else (if x<3250 then 1 else (if x<3274 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5789 : Finset ℕ := ([1596,1650,1678,1720,3072,3126,3130,3150,3188,3192,3250,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5789 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5789 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5789 3126 3
  · have he : independentCachedBranchMembers5789.erase 3126=independentCachedBranchMembers5787 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5787
  · have he : independentCachedBranchMembers5789.filter (independentCachedEdge 3126)=independentCachedBranchMembers5788 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5788
def independentCachedBranchMembers5790 : Finset ℕ := ([1596,1628,1642,1650,1678,1686,1708,1720,1748,1752,3072,3118,3126,3130,3150,3158,3162,3180,3188,3192,3228,3238,3242,3250,3270,3274,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5790 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5790 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5790 1708 4
  · have he : independentCachedBranchMembers5790.erase 1708=independentCachedBranchMembers5786 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5786
  · have he : independentCachedBranchMembers5790.filter (independentCachedEdge 1708)=independentCachedBranchMembers5789 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5789
def independentCachedBranchMembers5791 : Finset ℕ := ([1596,1628,1642,1650,1678,1686,1720,1752,3130,3162,3180,3188,3238,3270,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound5791 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5791 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5791 4 (fun x => (if x<3130 then (if x<1678 then (if x<1642 then (if x<1628 then 0 else 1) else (if x<1650 then 0 else 1)) else (if x<1720 then (if x<1686 then 0 else 1) else (if x<1752 then 1 else 0))) else (if x<3238 then (if x<3180 then (if x<3162 then 2 else 3) else (if x<3188 then 2 else 3)) else (if x<3304 then (if x<3270 then 2 else 3) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
