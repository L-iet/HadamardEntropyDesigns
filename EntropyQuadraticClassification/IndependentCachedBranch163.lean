/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch162
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8000 : Finset ℕ := ([66,136,246,1596,1628,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8000 136 4
  · have he : independentCachedBranchMembers8000.erase 136=independentCachedBranchMembers7998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7998
  · have he : independentCachedBranchMembers8000.filter (independentCachedEdge 136)=independentCachedBranchMembers7999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7999
def independentCachedBranchMembers8001 : Finset ℕ := ([66,1596,1686,1720,1734,1768,2646,2680,2770,3158,3192,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8001 4 (fun x => (if x<2646 then (if x<1720 then (if x<1596 then 0 else (if x<1686 then 0 else 1)) else (if x<1734 then 1 else (if x<1768 then 2 else 2))) else (if x<3158 then (if x<2680 then 1 else (if x<2770 then 1 else 0)) else (if x<3192 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8002 : Finset ℕ := ([34,66,136,246,1596,1628,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8002 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8002 34 4
  · have he : independentCachedBranchMembers8002.erase 34=independentCachedBranchMembers8000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8000
  · have he : independentCachedBranchMembers8002.filter (independentCachedEdge 34)=independentCachedBranchMembers8001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8001
def independentCachedBranchMembers8003 : Finset ℕ := ([136,1628,1702,1720,1768,2614,2662,2680,2716,2764,2770,3158,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8003 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8003 4 (fun x => (if x<2680 then (if x<1720 then (if x<1628 then 0 else (if x<1702 then 1 else 2)) else (if x<2614 then (if x<1768 then 0 else 1) else (if x<2662 then 2 else 0))) else (if x<3158 then (if x<2764 then (if x<2716 then 1 else 3) else (if x<2770 then 1 else 3)) else (if x<3250 then (if x<3244 then 0 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8004 : Finset ℕ := ([1720,1768,2680,2770,3158,3244] : List ℕ).toFinset
theorem independentCachedBranchBound8004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8004 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8004 3 (fun x => (if x<2770 then (if x<1768 then 0 else (if x<2680 then 1 else 0)) else (if x<3158 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8005 : Finset ℕ := ([34,136,1628,1702,1720,1768,2614,2662,2680,2716,2764,2770,3158,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8005 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8005 34 3
  · have he : independentCachedBranchMembers8005.erase 34=independentCachedBranchMembers8003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8003
  · have he : independentCachedBranchMembers8005.filter (independentCachedEdge 34)=independentCachedBranchMembers8004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8004
def independentCachedBranchMembers8006 : Finset ℕ := ([34,66,136,246,1596,1628,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8006 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8006 3282 4
  · have he : independentCachedBranchMembers8006.erase 3282=independentCachedBranchMembers8002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8002
  · have he : independentCachedBranchMembers8006.filter (independentCachedEdge 3282)=independentCachedBranchMembers8005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8005
def independentCachedBranchMembers8007 : Finset ℕ := ([246,1596,1686,1702,1720,2646,2662,2680,2764,2770,2786,3126,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8007 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8007 4 (fun x => (if x<2680 then (if x<1702 then (if x<1596 then 0 else (if x<1686 then 1 else 0)) else (if x<2646 then (if x<1720 then 1 else 2) else (if x<2662 then 0 else 2))) else (if x<3126 then (if x<2770 then (if x<2764 then 1 else 3) else (if x<2786 then 3 else 1)) else (if x<3244 then (if x<3228 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8008 : Finset ℕ := ([1686,1702,2680,2764,3126,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8008 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8008 3 (fun x => (if x<2764 then (if x<1702 then 0 else (if x<2680 then 1 else 0)) else (if x<3126 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8009 : Finset ℕ := ([66,246,1596,1686,1702,1720,2646,2662,2680,2764,2770,2786,3126,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8009 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8009 66 3
  · have he : independentCachedBranchMembers8009.erase 66=independentCachedBranchMembers8007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8007
  · have he : independentCachedBranchMembers8009.filter (independentCachedEdge 66)=independentCachedBranchMembers8008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8008
def independentCachedBranchMembers8010 : Finset ℕ := ([34,66,136,246,1596,1628,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8010 3276 4
  · have he : independentCachedBranchMembers8010.erase 3276=independentCachedBranchMembers8006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8006
  · have he : independentCachedBranchMembers8010.filter (independentCachedEdge 3276)=independentCachedBranchMembers8009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8009
def independentCachedBranchMembers8011 : Finset ℕ := ([66,136,1596,1734,1752,1768,2614,2764,2770,2786,3158,3174,3192,3228,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound8011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8011 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8011 4 (fun x => (if x<2770 then (if x<1752 then (if x<1596 then (if x<136 then 0 else 0) else (if x<1734 then 1 else 2)) else (if x<2614 then (if x<1768 then 1 else 2) else (if x<2764 then 1 else 2))) else (if x<3192 then (if x<3158 then (if x<2786 then 1 else 2) else (if x<3174 then 0 else 3)) else (if x<3244 then (if x<3228 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8012 : Finset ℕ := ([34,66,136,246,1596,1628,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2738,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8012 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8012 2738 4
  · have he : independentCachedBranchMembers8012.erase 2738=independentCachedBranchMembers8010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8010
  · have he : independentCachedBranchMembers8012.filter (independentCachedEdge 2738)=independentCachedBranchMembers8011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8011
def independentCachedBranchMembers8013 : Finset ℕ := ([34,246,1628,1686,1734,1752,2646,2716,2764,2770,3126,3174,3192,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8013 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8013 4 (fun x => (if x<2764 then (if x<1734 then (if x<1628 then (if x<246 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1752 then 2 else 2) else (if x<2716 then 1 else 1))) else (if x<3192 then (if x<3126 then (if x<2770 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3298 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8014 : Finset ℕ := ([34,66,136,246,1596,1628,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2732,2738,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8014 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8014 2732 4
  · have he : independentCachedBranchMembers8014.erase 2732=independentCachedBranchMembers8012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8012
  · have he : independentCachedBranchMembers8014.filter (independentCachedEdge 2732)=independentCachedBranchMembers8013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8013
def independentCachedBranchMembers8015 : Finset ℕ := ([34,66,136,246,1596,1628,1686,1768,2614,2646,2716,2786,3126,3158,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8015 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8015 4 (fun x => (if x<2614 then (if x<1596 then (if x<136 then (if x<66 then 0 else 1) else (if x<246 then 0 else 1)) else (if x<1686 then (if x<1628 then 2 else 3) else (if x<1768 then 2 else 3))) else (if x<3126 then (if x<2716 then (if x<2646 then 0 else 1) else (if x<2786 then 0 else 1)) else (if x<3228 then (if x<3158 then 2 else 3) else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8016 : Finset ℕ := ([34,66,136,246,1596,1628,1644,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2732,2738,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8016 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8016 1644 4
  · have he : independentCachedBranchMembers8016.erase 1644=independentCachedBranchMembers8014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8014
  · have he : independentCachedBranchMembers8016.filter (independentCachedEdge 1644)=independentCachedBranchMembers8015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8015
def independentCachedBranchMembers8017 : Finset ℕ := ([34,66,1596,1628,1702,1720,1734,1752,2662,2680,2716,2786,3174,3192,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8017 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8017 4 (fun x => (if x<2662 then (if x<1702 then (if x<1596 then (if x<66 then 0 else 1) else (if x<1628 then 1 else 0)) else (if x<1734 then (if x<1720 then 2 else 2) else (if x<1752 then 3 else 3))) else (if x<3174 then (if x<2716 then (if x<2680 then 2 else 2) else (if x<2786 then 0 else 1)) else (if x<3228 then (if x<3192 then 3 else 3) else (if x<3298 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8018 : Finset ℕ := ([18,34,66,136,246,1596,1628,1644,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2732,2738,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8018 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8018 18 4
  · have he : independentCachedBranchMembers8018.erase 18=independentCachedBranchMembers8016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8016
  · have he : independentCachedBranchMembers8018.filter (independentCachedEdge 18)=independentCachedBranchMembers8017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8017
def independentCachedBranchMembers8019 : Finset ℕ := ([246,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,3126,3158,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8019 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8019 4 (fun x => (if x<2614 then (if x<1720 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 2) else (if x<1768 then 2 else 3))) else (if x<3126 then (if x<2662 then (if x<2646 then 0 else 3) else (if x<2680 then 1 else 1)) else (if x<3174 then (if x<3158 then 3 else 0) else (if x<3192 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8020 : Finset ℕ := ([246,1686,1702,1734,2680,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8020 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8020 3 (fun x => (if x<1734 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<2680 then 2 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8021 : Finset ℕ := ([136,246,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,3126,3158,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound8021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8021 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8021 136 3
  · have he : independentCachedBranchMembers8021.erase 136=independentCachedBranchMembers8019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8019
  · have he : independentCachedBranchMembers8021.filter (independentCachedEdge 136)=independentCachedBranchMembers8020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8020
def independentCachedBranchMembers8022 : Finset ℕ := ([12,18,34,66,136,246,1596,1628,1644,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2732,2738,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound8022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8022 12 4
  · have he : independentCachedBranchMembers8022.erase 12=independentCachedBranchMembers8018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8018
  · have he : independentCachedBranchMembers8022.filter (independentCachedEdge 12)=independentCachedBranchMembers8021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8021
def independentCachedBranchMembers8023 : Finset ℕ := ([10,12,18,20,34,36,66,68,136,144,160,190,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2560,2590,2606,2614,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound8023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8023 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8023 10 5
  · have he : independentCachedBranchMembers8023.erase 10=independentCachedBranchMembers7997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7997
  · have he : independentCachedBranchMembers8023.filter (independentCachedEdge 10)=independentCachedBranchMembers8022 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8022
def independentCachedBranchMembers8024 : Finset ℕ := ([10,12,18,20,34,36,40,48,66,68,72,80,130,132,136,144,160,190,192,222,238,246,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1656,1678,1686,1690,1692,1702,1706,1708,1714,1716,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2560,2590,2606,2614,2618,2620,2638,2646,2650,2652,2662,2666,2668,2674,2676,2680,2702,2710,2714,2716,2726,2730,2732,2738,2740,2744,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8024 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8024 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8024 1656 6
  · have he : independentCachedBranchMembers8024.erase 1656=independentCachedBranchMembers7564 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7564
  · have he : independentCachedBranchMembers8024.filter (independentCachedEdge 1656)=independentCachedBranchMembers8023 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8023
def independentCachedBranchMembers8025 : Finset ℕ := ([1590,1614,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2662,2680,2732,2738,2762,2772,3130,3132,3162,3164,3174,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8025 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8025 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8025 6 (fun x => (if x<2732 then (if x<1702 then (if x<1650 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1644 then 1 else 2)) else (if x<1690 then (if x<1652 then 2 else 1) else (if x<1692 then 0 else 3))) else (if x<1762 then (if x<1734 then (if x<1720 then 1 else 1) else (if x<1752 then 2 else 2)) else (if x<2662 then (if x<1764 then 0 else 3) else (if x<2680 then 0 else 1)))) else (if x<3174 then (if x<3130 then (if x<2762 then (if x<2738 then 3 else 0) else (if x<2772 then 0 else 3)) else (if x<3162 then (if x<3132 then 4 else 5) else (if x<3164 then 5 else 4))) else (if x<3252 then (if x<3222 then (if x<3214 then 2 else 4) else (if x<3242 then 5 else 5)) else (if x<3282 then (if x<3276 then 3 else 2) else (if x<3304 then 2 else (if x<3312 then 4 else 5)))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8026 : Finset ℕ := ([1590,1614,1650,1652,1720,1734,2680,2738,2762,3130,3132,3214,3252,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8026 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8026 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8026 5 (fun x => (if x<2738 then (if x<1652 then (if x<1614 then 0 else (if x<1650 then 0 else 1)) else (if x<1734 then (if x<1720 then 2 else 1) else (if x<2680 then 2 else 1))) else (if x<3214 then (if x<3130 then (if x<2762 then 0 else 0) else (if x<3132 then 1 else 2)) else (if x<3276 then (if x<3252 then 2 else 0) else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8027 : Finset ℕ := ([1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2662,2680,2732,2738,2762,2772,3130,3132,3162,3164,3174,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8027 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8027 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8027 1622 5
  · have he : independentCachedBranchMembers8027.erase 1622=independentCachedBranchMembers8025 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8025
  · have he : independentCachedBranchMembers8027.filter (independentCachedEdge 1622)=independentCachedBranchMembers8026 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8026
def independentCachedBranchMembers8028 : Finset ℕ := ([1590,1614,1642,1644,1702,1752,2680,2738,2762,3162,3164,3222,3252,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8028 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8028 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8028 5 (fun x => (if x<2738 then (if x<1644 then (if x<1614 then 0 else (if x<1642 then 0 else 1)) else (if x<1752 then (if x<1702 then 2 else 1) else (if x<2680 then 2 else 1))) else (if x<3222 then (if x<3162 then (if x<2762 then 0 else 0) else (if x<3164 then 1 else 2)) else (if x<3276 then (if x<3252 then 1 else 0) else (if x<3304 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8029 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2662,2680,2732,2738,2762,2772,3130,3132,3162,3164,3174,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8029 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8029 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8029 1582 5
  · have he : independentCachedBranchMembers8029.erase 1582=independentCachedBranchMembers8027 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8027
  · have he : independentCachedBranchMembers8029.filter (independentCachedEdge 1582)=independentCachedBranchMembers8028 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8028
def independentCachedBranchMembers8030 : Finset ℕ := ([1590,1622,1642,1644,1690,1692,1702,1734,2680,2738,2772,3130,3132,3162,3164,3174,3222,3242,3276,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8030 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8030 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8030 5 (fun x => (if x<2772 then (if x<1692 then (if x<1642 then (if x<1622 then 0 else 1) else (if x<1644 then 0 else (if x<1690 then 1 else 0))) else (if x<1734 then (if x<1702 then 1 else 1) else (if x<2680 then 0 else (if x<2738 then 2 else 2)))) else (if x<3174 then (if x<3132 then (if x<3130 then 2 else 0) else (if x<3162 then 3 else (if x<3164 then 3 else 1))) else (if x<3242 then (if x<3222 then 0 else 0) else (if x<3276 then 3 else (if x<3312 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8031 : Finset ℕ := ([1582,1590,1614,1622,1642,1644,1650,1652,1690,1692,1702,1720,1734,1752,1762,1764,2662,2680,2732,2738,2762,2772,2800,3130,3132,3162,3164,3174,3214,3222,3242,3252,3276,3282,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8031 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8031 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8031 2800 5
  · have he : independentCachedBranchMembers8031.erase 2800=independentCachedBranchMembers8029 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8029
  · have he : independentCachedBranchMembers8031.filter (independentCachedEdge 2800)=independentCachedBranchMembers8030 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8030
end EntropyDesigns.QuadraticRefinement
