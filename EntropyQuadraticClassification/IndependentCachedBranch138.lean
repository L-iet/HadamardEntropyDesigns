/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch137
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7200 : Finset ℕ := ([48,68,144,238,1614,1644,1690,1714,1720,1734,1740,1764,2618,2638,2662,2668,2714,2738,2758,2764,3130,3150,3174,3180,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7200 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7200 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7200 5 (fun x => (if x<2662 then (if x<1714 then (if x<238 then (if x<68 then 0 else (if x<144 then 0 else 1)) else (if x<1644 then (if x<1614 then 2 else 0) else (if x<1690 then 1 else 3))) else (if x<1740 then (if x<1720 then 4 else (if x<1734 then 1 else 2)) else (if x<2618 then (if x<1764 then 3 else 4) else (if x<2638 then 3 else 1)))) else (if x<3150 then (if x<2738 then (if x<2668 then 2 else (if x<2714 then 3 else 1)) else (if x<2764 then (if x<2758 then 0 else 0) else (if x<3130 then 2 else 4))) else (if x<3250 then (if x<3174 then 2 else (if x<3180 then 1 else 4)) else (if x<3276 then (if x<3256 then 1 else 0) else (if x<3300 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7201 : Finset ℕ := ([48,144,238,1614,1720,1734,2638,2662,2758,3150,3174,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7201 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7201 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7201 4 (fun x => (if x<2638 then (if x<1614 then (if x<144 then 0 else (if x<238 then 1 else 2)) else (if x<1720 then 0 else (if x<1734 then 1 else 2))) else (if x<3150 then (if x<2662 then 1 else (if x<2758 then 2 else 0)) else (if x<3174 then 2 else (if x<3256 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7202 : Finset ℕ := ([18,48,68,144,238,1614,1644,1690,1714,1720,1734,1740,1764,2618,2638,2662,2668,2714,2738,2758,2764,3130,3150,3174,3180,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7202 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7202 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7202 18 4
  · have he : independentCachedBranchMembers7202.erase 18=independentCachedBranchMembers7200 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7200
  · have he : independentCachedBranchMembers7202.filter (independentCachedEdge 18)=independentCachedBranchMembers7201 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7201
def independentCachedBranchMembers7203 : Finset ℕ := ([48,238,1614,1690,1734,1740,2638,2714,2758,2764,3130,3174,3180,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7203 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7203 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7203 4 (fun x => (if x<2758 then (if x<1734 then (if x<1614 then (if x<238 then 0 else 1) else (if x<1690 then 0 else 2)) else (if x<2638 then (if x<1740 then 1 else 2) else (if x<2714 then 1 else 3))) else (if x<3180 then (if x<3130 then (if x<2764 then 0 else 3) else (if x<3174 then 2 else 1)) else (if x<3256 then (if x<3250 then 2 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7204 : Finset ℕ := ([18,48,68,144,238,1614,1644,1690,1714,1720,1734,1740,1764,2618,2638,2662,2668,2714,2738,2758,2764,3130,3150,3174,3180,3226,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7204 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7204 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7204 3226 4
  · have he : independentCachedBranchMembers7204.erase 3226=independentCachedBranchMembers7202 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7202
  · have he : independentCachedBranchMembers7204.filter (independentCachedEdge 3226)=independentCachedBranchMembers7203 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7203
def independentCachedBranchMembers7205 : Finset ℕ := ([48,144,1614,1714,1720,1764,2618,2662,2668,2714,2758,2764,3150,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7205 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7205 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7205 4 (fun x => (if x<2668 then (if x<1720 then (if x<1614 then (if x<144 then 0 else 1) else (if x<1714 then 0 else 1)) else (if x<2618 then (if x<1764 then 2 else 2) else (if x<2662 then 2 else 2))) else (if x<3150 then (if x<2758 then (if x<2714 then 1 else 3) else (if x<2764 then 0 else 3)) else (if x<3256 then (if x<3250 then 1 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7206 : Finset ℕ := ([18,48,68,144,238,1614,1644,1690,1714,1720,1734,1740,1764,2618,2638,2662,2668,2714,2738,2758,2764,2788,3130,3150,3174,3180,3226,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7206 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7206 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7206 2788 4
  · have he : independentCachedBranchMembers7206.erase 2788=independentCachedBranchMembers7204 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7204
  · have he : independentCachedBranchMembers7206.filter (independentCachedEdge 2788)=independentCachedBranchMembers7205 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7205
def independentCachedBranchMembers7207 : Finset ℕ := ([144,238,1690,1714,1720,1734,1740,1764,2618,2638,2662,2668,3130,3150,3174,3180] : List ℕ).toFinset
theorem independentCachedBranchBound7207 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7207 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7207 4 (fun x => (if x<2618 then (if x<1720 then (if x<1690 then (if x<238 then 0 else 1) else (if x<1714 then 0 else 2)) else (if x<1740 then (if x<1734 then 3 else 1) else (if x<1764 then 3 else 2))) else (if x<3130 then (if x<2662 then (if x<2638 then 2 else 1) else (if x<2668 then 0 else 2)) else (if x<3174 then (if x<3150 then 3 else 3) else (if x<3180 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7208 : Finset ℕ := ([18,48,68,144,238,1594,1614,1644,1690,1714,1720,1734,1740,1764,2618,2638,2662,2668,2714,2738,2758,2764,2788,3130,3150,3174,3180,3226,3250,3256,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7208 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7208 1594 4
  · have he : independentCachedBranchMembers7208.erase 1594=independentCachedBranchMembers7206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7206
  · have he : independentCachedBranchMembers7208.filter (independentCachedEdge 1594)=independentCachedBranchMembers7207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7207
def independentCachedBranchMembers7209 : Finset ℕ := ([12,18,48,68,80,132,144,238,250,1582,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7209 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7209 80 5
  · have he : independentCachedBranchMembers7209.erase 80=independentCachedBranchMembers7199 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7199
  · have he : independentCachedBranchMembers7209.filter (independentCachedEdge 80)=independentCachedBranchMembers7208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7208
def independentCachedBranchMembers7210 : Finset ℕ := ([48,132,250,1594,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7210 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7210 5 (fun x => (if x<2674 then (if x<1720 then (if x<1594 then (if x<132 then 0 else (if x<250 then 0 else 1)) else (if x<1678 then 0 else (if x<1714 then 0 else 1))) else (if x<1776 then (if x<1734 then 2 else (if x<1740 then 3 else 2)) else (if x<2618 then 3 else (if x<2638 then 1 else 2)))) else (if x<3150 then (if x<2764 then (if x<2680 then 0 else (if x<2758 then 3 else 0)) else (if x<2800 then 4 else (if x<3130 then 1 else 4))) else (if x<3214 then (if x<3186 then 4 else (if x<3192 then 1 else 0)) else (if x<3250 then 3 else (if x<3256 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7211 : Finset ℕ := ([132,250,1678,1776,2674,2680,2800,3186,3192,3214] : List ℕ).toFinset
theorem independentCachedBranchBound7211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7211 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7211 4 (fun x => (if x<2680 then (if x<1678 then (if x<250 then 0 else 1) else (if x<1776 then 0 else (if x<2674 then 1 else 0))) else (if x<3186 then (if x<2800 then 1 else 2) else (if x<3192 then 1 else (if x<3214 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7212 : Finset ℕ := ([48,68,132,250,1594,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7212 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7212 68 4
  · have he : independentCachedBranchMembers7212.erase 68=independentCachedBranchMembers7210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7210
  · have he : independentCachedBranchMembers7212.filter (independentCachedEdge 68)=independentCachedBranchMembers7211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7211
def independentCachedBranchMembers7213 : Finset ℕ := ([250,1720,1740,1776,2680,2764,2800,3130,3150,3186,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7213 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7213 4 (fun x => (if x<2800 then (if x<1776 then (if x<1720 then 0 else (if x<1740 then 0 else 1)) else (if x<2680 then 1 else (if x<2764 then 0 else 2))) else (if x<3186 then (if x<3130 then 2 else (if x<3150 then 0 else 1)) else (if x<3214 then 1 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7214 : Finset ℕ := ([48,68,132,250,1594,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7214 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7214 3276 4
  · have he : independentCachedBranchMembers7214.erase 3276=independentCachedBranchMembers7212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7212
  · have he : independentCachedBranchMembers7214.filter (independentCachedEdge 3276)=independentCachedBranchMembers7213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7213
def independentCachedBranchMembers7215 : Finset ℕ := ([132,1678,1714,1734,2618,2638,2674,2764,2800,3192,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7215 4 (fun x => (if x<2674 then (if x<1734 then (if x<1678 then 0 else (if x<1714 then 0 else 1)) else (if x<2618 then 1 else (if x<2638 then 1 else 1))) else (if x<3192 then (if x<2764 then 0 else (if x<2800 then 2 else 2)) else (if x<3214 then 0 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7216 : Finset ℕ := ([48,68,132,250,1594,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2738,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7216 2738 4
  · have he : independentCachedBranchMembers7216.erase 2738=independentCachedBranchMembers7214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7214
  · have he : independentCachedBranchMembers7216.filter (independentCachedEdge 2738)=independentCachedBranchMembers7215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7215
def independentCachedBranchMembers7217 : Finset ℕ := ([68,1594,1678,1714,1740,1776,2638,2674,2758,3150,3186,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7217 4 (fun x => (if x<2638 then (if x<1714 then (if x<1594 then 0 else (if x<1678 then 0 else 1)) else (if x<1740 then 1 else (if x<1776 then 2 else 2))) else (if x<3150 then (if x<2674 then 1 else (if x<2758 then 1 else 0)) else (if x<3186 then 2 else (if x<3256 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7218 : Finset ℕ := ([48,68,132,250,1594,1650,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2738,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7218 1650 4
  · have he : independentCachedBranchMembers7218.erase 1650=independentCachedBranchMembers7216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7216
  · have he : independentCachedBranchMembers7218.filter (independentCachedEdge 1650)=independentCachedBranchMembers7217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7217
def independentCachedBranchMembers7219 : Finset ℕ := ([68,132,250,1594,1720,1734,2618,2680,2758,3130,3192,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7219 4 (fun x => (if x<2618 then (if x<1594 then (if x<132 then 0 else (if x<250 then 1 else 2)) else (if x<1720 then 0 else (if x<1734 then 2 else 1))) else (if x<3130 then (if x<2680 then 1 else (if x<2758 then 2 else 0)) else (if x<3192 then 2 else (if x<3256 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7220 : Finset ℕ := ([12,48,68,132,250,1594,1650,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2738,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound7220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7220 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7220 12 4
  · have he : independentCachedBranchMembers7220.erase 12=independentCachedBranchMembers7218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7218
  · have he : independentCachedBranchMembers7220.filter (independentCachedEdge 12)=independentCachedBranchMembers7219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7219
def independentCachedBranchMembers7221 : Finset ℕ := ([68,132,1594,1734,1740,1776,2618,2758,2764,2800,3150,3186,3192,3214,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7221 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7221 4 (fun x => (if x<2764 then (if x<1740 then (if x<1594 then (if x<132 then 0 else 1) else (if x<1734 then 0 else 1)) else (if x<2618 then (if x<1776 then 2 else 2) else (if x<2758 then 1 else 0))) else (if x<3192 then (if x<3150 then (if x<2800 then 3 else 3) else (if x<3186 then 2 else 2)) else (if x<3250 then (if x<3214 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7222 : Finset ℕ := ([12,48,68,132,250,1594,1650,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2738,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7222 3312 4
  · have he : independentCachedBranchMembers7222.erase 3312=independentCachedBranchMembers7220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7220
  · have he : independentCachedBranchMembers7222.filter (independentCachedEdge 3312)=independentCachedBranchMembers7221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7221
def independentCachedBranchMembers7223 : Finset ℕ := ([68,250,1594,1678,1714,1720,2638,2674,2680,2758,2764,2800,3130,3214,3250,3256] : List ℕ).toFinset
theorem independentCachedBranchBound7223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7223 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7223 4 (fun x => (if x<2680 then (if x<1714 then (if x<1594 then (if x<250 then 0 else 1) else (if x<1678 then 0 else 2)) else (if x<2638 then (if x<1720 then 1 else 2) else (if x<2674 then 2 else 1))) else (if x<3130 then (if x<2764 then (if x<2758 then 2 else 0) else (if x<2800 then 3 else 3)) else (if x<3250 then (if x<3214 then 1 else 3) else (if x<3256 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7224 : Finset ℕ := ([12,48,68,132,250,1594,1650,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2702,2738,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7224 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7224 2702 4
  · have he : independentCachedBranchMembers7224.erase 2702=independentCachedBranchMembers7222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7222
  · have he : independentCachedBranchMembers7224.filter (independentCachedEdge 2702)=independentCachedBranchMembers7223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7223
def independentCachedBranchMembers7225 : Finset ℕ := ([250,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,3130,3150,3186,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7225 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7225 4 (fun x => (if x<2618 then (if x<1720 then (if x<1678 then 0 else (if x<1714 then 1 else 0)) else (if x<1740 then (if x<1734 then 1 else 2) else (if x<1776 then 3 else 2))) else (if x<3130 then (if x<2674 then (if x<2638 then 0 else 1) else (if x<2680 then 3 else 1)) else (if x<3186 then (if x<3150 then 3 else 2) else (if x<3192 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7226 : Finset ℕ := ([250,1714,1720,1776,2638,3150] : List ℕ).toFinset
theorem independentCachedBranchBound7226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7226 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7226 3 (fun x => (if x<1776 then (if x<1714 then 0 else (if x<1720 then 0 else 1)) else (if x<2638 then 2 else (if x<3150 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7227 : Finset ℕ := ([132,250,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,3130,3150,3186,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7227 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7227 132 3
  · have he : independentCachedBranchMembers7227.erase 132=independentCachedBranchMembers7225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7225
  · have he : independentCachedBranchMembers7227.filter (independentCachedEdge 132)=independentCachedBranchMembers7226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7226
def independentCachedBranchMembers7228 : Finset ℕ := ([12,48,68,132,250,1594,1614,1650,1678,1714,1720,1734,1740,1776,2618,2638,2674,2680,2702,2738,2758,2764,2800,3130,3150,3186,3192,3214,3250,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7228 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7228 1614 4
  · have he : independentCachedBranchMembers7228.erase 1614=independentCachedBranchMembers7224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7224
  · have he : independentCachedBranchMembers7228.filter (independentCachedEdge 1614)=independentCachedBranchMembers7227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7227
def independentCachedBranchMembers7229 : Finset ℕ := ([12,18,36,48,68,80,132,144,238,250,1582,1594,1614,1626,1644,1650,1678,1690,1702,1708,1714,1720,1734,1740,1746,1752,1764,1776,2606,2618,2638,2650,2662,2668,2674,2680,2702,2714,2732,2738,2758,2764,2770,2776,2788,2800,3118,3130,3150,3162,3174,3180,3186,3192,3214,3226,3238,3244,3250,3256,3276,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7229 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7229 36 5
  · have he : independentCachedBranchMembers7229.erase 36=independentCachedBranchMembers7209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7209
  · have he : independentCachedBranchMembers7229.filter (independentCachedEdge 36)=independentCachedBranchMembers7228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7228
def independentCachedBranchMembers7230 : Finset ℕ := ([68,132,238,1594,1614,1678,1708,1714,1734,1752,1764,2618,2638,2668,2674,2702,2758,2776,2788,3118,3162,3174,3192,3226,3238,3256,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound7230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7230 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7230 5 (fun x => (if x<2674 then (if x<1714 then (if x<1594 then (if x<132 then 0 else (if x<238 then 1 else 0)) else (if x<1678 then (if x<1614 then 1 else 0) else (if x<1708 then 1 else 2))) else (if x<1764 then (if x<1734 then 2 else (if x<1752 then 2 else 2)) else (if x<2638 then (if x<2618 then 0 else 3) else (if x<2668 then 3 else 0)))) else (if x<3174 then (if x<2776 then (if x<2702 then 1 else (if x<2758 then 4 else 0)) else (if x<3118 then (if x<2788 then 3 else 4) else (if x<3162 then 3 else 3))) else (if x<3238 then (if x<3192 then 0 else (if x<3226 then 1 else 4)) else (if x<3276 then (if x<3256 then 2 else 2) else (if x<3312 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7231 : Finset ℕ := ([238,1708,1752,1764,2668,2776,2788,3118,3162,3174,3226,3238] : List ℕ).toFinset
theorem independentCachedBranchBound7231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7231 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7231 4 (fun x => (if x<2788 then (if x<1764 then (if x<1708 then 0 else (if x<1752 then 0 else 1)) else (if x<2668 then 1 else (if x<2776 then 0 else 2))) else (if x<3174 then (if x<3118 then 2 else (if x<3162 then 0 else 1)) else (if x<3226 then 1 else (if x<3238 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
