/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch121
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers6688 : Finset ℕ := ([72,80,250,252,1626,1628,1642,1652,1734,1752,1768,1776,2650,2652,2668,2674,2758,2776,2792,2800,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6688 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6688 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6688 5 (fun x => (if x<2674 then (if x<1652 then (if x<252 then (if x<80 then 0 else (if x<250 then 1 else 0)) else (if x<1628 then (if x<1626 then 1 else 0) else (if x<1642 then 1 else 2))) else (if x<1776 then (if x<1752 then (if x<1734 then 2 else 2) else (if x<1768 then 2 else 0)) else (if x<2652 then (if x<2650 then 1 else 3) else (if x<2668 then 4 else 3)))) else (if x<3174 then (if x<2792 then (if x<2758 then 4 else (if x<2776 then 3 else 0)) else (if x<3150 then (if x<2800 then 4 else 3) else (if x<3158 then 3 else 4))) else (if x<3282 then (if x<3274 then (if x<3192 then 2 else 0) else (if x<3276 then 0 else 4)) else (if x<3298 then (if x<3284 then 3 else 1) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6689 : Finset ℕ := ([252,1626,1642,1652,1776,2652,2668,2674,2758,2776,2792,3150,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6689 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6689 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6689 4 (fun x => (if x<2674 then (if x<1652 then (if x<1626 then 0 else (if x<1642 then 1 else 2)) else (if x<2652 then (if x<1776 then 0 else 1) else (if x<2668 then 0 else 2))) else (if x<3150 then (if x<2776 then (if x<2758 then 1 else 3) else (if x<2792 then 1 else 3)) else (if x<3284 then (if x<3274 then 2 else 3) else (if x<3300 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6690 : Finset ℕ := ([1652,1776,2674,2758,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6690 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6690 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6690 3 (fun x => (if x<2758 then (if x<1776 then 0 else (if x<2674 then 1 else 0)) else (if x<3284 then 2 else (if x<3300 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6691 : Finset ℕ := ([72,252,1626,1642,1652,1776,2652,2668,2674,2758,2776,2792,3150,3274,3284,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6691 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6691 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6691 72 3
  · have he : independentCachedBranchMembers6691.erase 72=independentCachedBranchMembers6689 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6689
  · have he : independentCachedBranchMembers6691.filter (independentCachedEdge 72)=independentCachedBranchMembers6690 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6690
def independentCachedBranchMembers6692 : Finset ℕ := ([72,80,250,252,1626,1628,1642,1650,1652,1734,1752,1768,1776,2650,2652,2668,2674,2758,2776,2792,2800,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6692 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6692 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6692 1650 4
  · have he : independentCachedBranchMembers6692.erase 1650=independentCachedBranchMembers6688 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6688
  · have he : independentCachedBranchMembers6692.filter (independentCachedEdge 1650)=independentCachedBranchMembers6691 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6691
def independentCachedBranchMembers6693 : Finset ℕ := ([250,1628,1642,1652,1768,2650,2668,2674,2758,2776,2800,3158,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6693 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6693 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6693 4 (fun x => (if x<2674 then (if x<1652 then (if x<1628 then 0 else (if x<1642 then 1 else 0)) else (if x<2650 then (if x<1768 then 2 else 1) else (if x<2668 then 0 else 1))) else (if x<3158 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 1 else 3)) else (if x<3284 then (if x<3274 then 2 else 0) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6694 : Finset ℕ := ([1642,1768,2668,2758,3274,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6694 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6694 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6694 3 (fun x => (if x<2758 then (if x<1768 then 0 else (if x<2668 then 1 else 0)) else (if x<3274 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6695 : Finset ℕ := ([80,250,1628,1642,1652,1768,2650,2668,2674,2758,2776,2800,3158,3274,3284,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6695 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6695 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6695 80 3
  · have he : independentCachedBranchMembers6695.erase 80=independentCachedBranchMembers6693 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6693
  · have he : independentCachedBranchMembers6695.filter (independentCachedEdge 80)=independentCachedBranchMembers6694 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6694
def independentCachedBranchMembers6696 : Finset ℕ := ([72,80,250,252,1626,1628,1642,1644,1650,1652,1734,1752,1768,1776,2650,2652,2668,2674,2758,2776,2792,2800,3150,3158,3174,3192,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound6696 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6696 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6696 1644 4
  · have he : independentCachedBranchMembers6696.erase 1644=independentCachedBranchMembers6692 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6692
  · have he : independentCachedBranchMembers6696.filter (independentCachedEdge 1644)=independentCachedBranchMembers6695 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6695
def independentCachedBranchMembers6697 : Finset ℕ := ([68,72,80,192,222,246,250,252,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1764,1768,1776,2638,2646,2650,2652,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6697 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6697 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6697 3270 5
  · have he : independentCachedBranchMembers6697.erase 3270=independentCachedBranchMembers6687 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6687
  · have he : independentCachedBranchMembers6697.filter (independentCachedEdge 3270)=independentCachedBranchMembers6696 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6696
def independentCachedBranchMembers6698 : Finset ℕ := ([68,80,192,222,246,252,1622,1628,1642,1652,1734,1740,1746,1752,1764,1776,2646,2652,2758,2776,2788,2800,3150,3162,3174,3192,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6698 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6698 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6698 5 (fun x => (if x<1764 then (if x<1628 then (if x<222 then (if x<80 then 0 else (if x<192 then 1 else 2)) else (if x<252 then (if x<246 then 0 else 1) else (if x<1622 then 2 else 0))) else (if x<1734 then (if x<1642 then 3 else (if x<1652 then 3 else 1)) else (if x<1746 then (if x<1740 then 3 else 0) else (if x<1752 then 1 else 2)))) else (if x<2800 then (if x<2652 then (if x<1776 then 2 else (if x<2646 then 3 else 1)) else (if x<2776 then (if x<2758 then 0 else 0) else (if x<2788 then 4 else 4))) else (if x<3192 then (if x<3162 then (if x<3150 then 1 else 0) else (if x<3174 then 4 else 4)) else (if x<3298 then (if x<3284 then 3 else 0) else (if x<3304 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6699 : Finset ℕ := ([68,80,246,252,1622,1628,1764,1776,2646,2652,2788,2800,3150,3162,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6699 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6699 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6699 4 (fun x => (if x<2646 then (if x<1622 then (if x<246 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1764 then (if x<1628 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3150 then (if x<2788 then (if x<2652 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3298 then (if x<3162 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6700 : Finset ℕ := ([68,80,192,222,246,252,1622,1628,1642,1652,1734,1740,1746,1752,1764,1776,2646,2652,2758,2776,2788,2800,3150,3162,3174,3192,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6700 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6700 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6700 3274 4
  · have he : independentCachedBranchMembers6700.erase 3274=independentCachedBranchMembers6698 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6698
  · have he : independentCachedBranchMembers6700.filter (independentCachedEdge 3274)=independentCachedBranchMembers6699 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6699
def independentCachedBranchMembers6701 : Finset ℕ := ([68,252,1628,1642,1652,1740,1746,1764,2646,2758,2776,2800,3150,3174,3192,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6701 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6701 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6701 4 (fun x => (if x<2646 then (if x<1652 then (if x<1628 then (if x<252 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1764 then 1 else 0))) else (if x<3150 then (if x<2776 then (if x<2758 then 2 else 3) else (if x<2800 then 2 else 3)) else (if x<3192 then (if x<3174 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6702 : Finset ℕ := ([68,80,192,222,246,252,1622,1628,1642,1652,1734,1740,1746,1752,1764,1776,2646,2652,2758,2770,2776,2788,2800,3150,3162,3174,3192,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6702 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6702 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6702 2770 4
  · have he : independentCachedBranchMembers6702.erase 2770=independentCachedBranchMembers6700 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6700
  · have he : independentCachedBranchMembers6702.filter (independentCachedEdge 2770)=independentCachedBranchMembers6701 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6701
def independentCachedBranchMembers6703 : Finset ℕ := ([80,246,1622,1642,1652,1740,1746,1776,2652,2758,2776,2788,3162,3174,3192,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6703 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6703 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6703 4 (fun x => (if x<2652 then (if x<1652 then (if x<1622 then (if x<246 then 0 else 0) else (if x<1642 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 1) else (if x<1776 then 1 else 0))) else (if x<3162 then (if x<2776 then (if x<2758 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3192 then (if x<3174 then 3 else 3) else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6704 : Finset ℕ := ([68,80,192,222,246,252,1622,1628,1642,1652,1734,1740,1746,1752,1764,1776,2646,2652,2758,2764,2770,2776,2788,2800,3150,3162,3174,3192,3274,3284,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6704 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6704 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6704 2764 4
  · have he : independentCachedBranchMembers6704.erase 2764=independentCachedBranchMembers6702 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6702
  · have he : independentCachedBranchMembers6704.filter (independentCachedEdge 2764)=independentCachedBranchMembers6703 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6703
def independentCachedBranchMembers6705 : Finset ℕ := ([68,72,80,192,222,246,250,252,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1764,1768,1776,2638,2646,2650,2652,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6705 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6705 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6705 3178 5
  · have he : independentCachedBranchMembers6705.erase 3178=independentCachedBranchMembers6697 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6697
  · have he : independentCachedBranchMembers6705.filter (independentCachedEdge 3178)=independentCachedBranchMembers6704 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6704
def independentCachedBranchMembers6706 : Finset ℕ := ([80,192,250,252,1626,1628,1740,1746,1768,1776,2638,2646,2668,2674,2776,2786,2788,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6706 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6706 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6706 5 (fun x => (if x<2674 then (if x<1740 then (if x<252 then (if x<192 then 0 else (if x<250 then 1 else 0)) else (if x<1626 then 1 else (if x<1628 then 0 else 2))) else (if x<1776 then (if x<1746 then 1 else (if x<1768 then 2 else 2)) else (if x<2646 then (if x<2638 then 0 else 3) else (if x<2668 then 2 else 2)))) else (if x<3192 then (if x<2788 then (if x<2776 then 0 else (if x<2786 then 0 else 2)) else (if x<3164 then (if x<3162 then 1 else 3) else (if x<3174 then 4 else 3))) else (if x<3282 then (if x<3274 then 0 else (if x<3276 then 4 else 3)) else (if x<3304 then (if x<3284 then 0 else 1) else (if x<3312 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6707 : Finset ℕ := ([250,252,1768,1776,2668,2674,2786,2788,3174,3192,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6707 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6707 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6707 4 (fun x => (if x<2786 then (if x<1776 then (if x<252 then 0 else (if x<1768 then 1 else 0)) else (if x<2668 then 1 else (if x<2674 then 2 else 2))) else (if x<3192 then (if x<2788 then 0 else (if x<3174 then 1 else 2)) else (if x<3304 then 2 else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6708 : Finset ℕ := ([80,192,222,250,252,1626,1628,1740,1746,1768,1776,2638,2646,2668,2674,2776,2786,2788,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6708 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6708 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6708 222 4
  · have he : independentCachedBranchMembers6708.erase 222=independentCachedBranchMembers6706 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6706
  · have he : independentCachedBranchMembers6708.filter (independentCachedEdge 222)=independentCachedBranchMembers6707 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6707
def independentCachedBranchMembers6709 : Finset ℕ := ([80,192,1746,1776,2646,2674,2786,2788,3174,3282,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6709 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6709 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6709 4 (fun x => (if x<2786 then (if x<1776 then (if x<192 then 0 else (if x<1746 then 1 else 0)) else (if x<2646 then 1 else (if x<2674 then 0 else 2))) else (if x<3282 then (if x<2788 then 1 else (if x<3174 then 2 else 2)) else (if x<3284 then 1 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6710 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1740,1746,1768,1776,2638,2646,2668,2674,2776,2786,2788,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6710 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6710 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6710 72 4
  · have he : independentCachedBranchMembers6710.erase 72=independentCachedBranchMembers6708 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6708
  · have he : independentCachedBranchMembers6710.filter (independentCachedEdge 72)=independentCachedBranchMembers6709 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6709
def independentCachedBranchMembers6711 : Finset ℕ := ([72,80,250,252,1626,1628,1768,1776,2638,2646,2786,2788,3162,3164,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6711 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6711 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6711 4 (fun x => (if x<2638 then (if x<1626 then (if x<250 then (if x<80 then 0 else 1) else (if x<252 then 0 else 1)) else (if x<1768 then (if x<1628 then 0 else 1) else (if x<1776 then 0 else 1))) else (if x<3162 then (if x<2786 then (if x<2646 then 2 else 3) else (if x<2788 then 2 else 3)) else (if x<3304 then (if x<3164 then 3 else 2) else (if x<3312 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6712 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1740,1746,1768,1776,2638,2646,2668,2674,2758,2776,2786,2788,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6712 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6712 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6712 2758 4
  · have he : independentCachedBranchMembers6712.erase 2758=independentCachedBranchMembers6710 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6710
  · have he : independentCachedBranchMembers6712.filter (independentCachedEdge 2758)=independentCachedBranchMembers6711 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6711
def independentCachedBranchMembers6713 : Finset ℕ := ([72,250,1628,1740,1746,1776,2638,2668,2674,2786,3162,3174,3192,3274,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6713 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6713 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6713 4 (fun x => (if x<2674 then (if x<1746 then (if x<1628 then (if x<250 then 0 else 0) else (if x<1740 then 1 else 2)) else (if x<2638 then (if x<1776 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3192 then (if x<3162 then (if x<2786 then 2 else 1) else (if x<3174 then 0 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3304 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6714 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1740,1746,1748,1768,1776,2638,2646,2668,2674,2758,2776,2786,2788,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6714 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6714 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6714 1748 4
  · have he : independentCachedBranchMembers6714.erase 1748=independentCachedBranchMembers6712 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6712
  · have he : independentCachedBranchMembers6714.filter (independentCachedEdge 1748)=independentCachedBranchMembers6713 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6713
def independentCachedBranchMembers6715 : Finset ℕ := ([80,252,1626,1740,1746,1768,2646,2668,2674,2788,3164,3174,3192,3274,3284,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6715 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6715 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6715 4 (fun x => (if x<2674 then (if x<1746 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1740 then 1 else 1)) else (if x<2646 then (if x<1768 then 2 else 2) else (if x<2668 then 2 else 2))) else (if x<3192 then (if x<3164 then (if x<2788 then 1 else 1) else (if x<3174 then 0 else 3)) else (if x<3284 then (if x<3274 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6716 : Finset ℕ := ([72,80,192,222,250,252,1626,1628,1738,1740,1746,1748,1768,1776,2638,2646,2668,2674,2758,2776,2786,2788,3162,3164,3174,3192,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6716 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6716 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6716 1738 4
  · have he : independentCachedBranchMembers6716.erase 1738=independentCachedBranchMembers6714 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6714
  · have he : independentCachedBranchMembers6716.filter (independentCachedEdge 1738)=independentCachedBranchMembers6715 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6715
def independentCachedBranchMembers6717 : Finset ℕ := ([68,72,80,192,222,246,250,252,1622,1626,1628,1642,1644,1650,1652,1734,1738,1740,1746,1748,1752,1764,1768,1776,2638,2646,2650,2652,2662,2668,2674,2680,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3150,3158,3162,3164,3174,3178,3188,3192,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound6717 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6717 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6717 2662 5
  · have he : independentCachedBranchMembers6717.erase 2662=independentCachedBranchMembers6705 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6705
  · have he : independentCachedBranchMembers6717.filter (independentCachedEdge 2662)=independentCachedBranchMembers6716 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6716
def independentCachedBranchMembers6718 : Finset ℕ := ([80,252,1628,1642,1650,1734,1746,1764,1768,1776,2646,2668,2680,2772,2776,2786,3150,3162,3188,3192,3276,3284,3288,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6718 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6718 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6718 5 (fun x => (if x<2680 then (if x<1746 then (if x<1642 then (if x<252 then 0 else (if x<1628 then 0 else 0)) else (if x<1650 then 1 else (if x<1734 then 2 else 1))) else (if x<1776 then (if x<1764 then 3 else (if x<1768 then 2 else 3)) else (if x<2646 then 0 else (if x<2668 then 3 else 3)))) else (if x<3188 then (if x<2786 then (if x<2772 then 0 else (if x<2776 then 0 else 3)) else (if x<3150 then 1 else (if x<3162 then 4 else 2))) else (if x<3284 then (if x<3192 then 0 else (if x<3276 then 4 else 2)) else (if x<3288 then 4 else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6719 : Finset ℕ := ([80,1642,1746,1776,2668,2772,2776,3162,3188,3192,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6719 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6719 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6719 4 (fun x => (if x<2776 then (if x<1776 then (if x<1642 then 0 else (if x<1746 then 1 else 0)) else (if x<2668 then 1 else (if x<2772 then 2 else 0))) else (if x<3192 then (if x<3162 then 2 else (if x<3188 then 3 else 3)) else (if x<3276 then 1 else (if x<3298 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
