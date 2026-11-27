/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch99
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers5984 : Finset ℕ := ([1590,1626,1642,1652,1692,1708,1714,1776,2606,2652,2674,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5984 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5984 5 (fun x => (if x<2730 then (if x<1714 then (if x<1652 then (if x<1626 then 0 else (if x<1642 then 0 else 1)) else (if x<1692 then 1 else (if x<1708 then 0 else 1))) else (if x<2652 then (if x<1776 then 1 else (if x<2606 then 0 else 2)) else (if x<2674 then 2 else (if x<2714 then 0 else 2)))) else (if x<3158 then (if x<2776 then (if x<2740 then 1 else (if x<2758 then 0 else 2)) else (if x<2792 then 0 else (if x<3130 then 2 else 3))) else (if x<3214 then (if x<3174 then 3 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 3 else 4) else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5985 : Finset ℕ := ([1590,1652,1692,1708,2606,2652,2740,2758,3158,3174,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound5985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5985 4 (fun x => (if x<2740 then (if x<1708 then (if x<1652 then 0 else (if x<1692 then 1 else 0)) else (if x<2606 then 1 else (if x<2652 then 2 else 2))) else (if x<3174 then (if x<2758 then 0 else (if x<3158 then 2 else 1)) else (if x<3214 then 3 else (if x<3276 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5986 : Finset ℕ := ([250,1590,1626,1642,1652,1692,1708,1714,1776,2606,2652,2674,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5986 250 4
  · have he : independentCachedBranchMembers5986.erase 250=independentCachedBranchMembers5984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5984
  · have he : independentCachedBranchMembers5986.filter (independentCachedEdge 250)=independentCachedBranchMembers5985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5985
def independentCachedBranchMembers5987 : Finset ℕ := ([1626,1642,1714,1776,2606,2652,2740,2758,3130,3192,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5987 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5987 4 (fun x => (if x<2740 then (if x<1776 then (if x<1642 then 0 else (if x<1714 then 1 else 0)) else (if x<2606 then 1 else (if x<2652 then 1 else 0))) else (if x<3192 then (if x<2758 then 0 else (if x<3130 then 2 else 2)) else (if x<3282 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5988 : Finset ℕ := ([136,250,1590,1626,1642,1652,1692,1708,1714,1776,2606,2652,2674,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5988 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5988 136 4
  · have he : independentCachedBranchMembers5988.erase 136=independentCachedBranchMembers5986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5986
  · have he : independentCachedBranchMembers5988.filter (independentCachedEdge 136)=independentCachedBranchMembers5987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5987
def independentCachedBranchMembers5989 : Finset ℕ := ([1590,1642,1692,1714,2714,2740,2758,2792,3130,3174,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5989 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5989 4 (fun x => (if x<2758 then (if x<1714 then (if x<1642 then 0 else (if x<1692 then 0 else 1)) else (if x<2714 then 1 else (if x<2740 then 1 else 0))) else (if x<3174 then (if x<2792 then 2 else (if x<3130 then 0 else 2)) else (if x<3276 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5990 : Finset ℕ := ([80,136,250,1590,1626,1642,1652,1692,1708,1714,1776,2606,2652,2674,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5990 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5990 80 4
  · have he : independentCachedBranchMembers5990.erase 80=independentCachedBranchMembers5988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5988
  · have he : independentCachedBranchMembers5990.filter (independentCachedEdge 80)=independentCachedBranchMembers5989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5989
def independentCachedBranchMembers5991 : Finset ℕ := ([1626,1652,1708,1776,2714,2740,2758,2792,3158,3192,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5991 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5991 4 (fun x => (if x<2758 then (if x<1776 then (if x<1652 then 0 else (if x<1708 then 0 else 1)) else (if x<2714 then 1 else (if x<2740 then 0 else 0))) else (if x<3192 then (if x<2792 then 2 else (if x<3158 then 1 else 2)) else (if x<3214 then 2 else (if x<3282 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5992 : Finset ℕ := ([34,80,136,250,1590,1626,1642,1652,1692,1708,1714,1776,2606,2652,2674,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5992 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5992 34 4
  · have he : independentCachedBranchMembers5992.erase 34=independentCachedBranchMembers5990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5990
  · have he : independentCachedBranchMembers5992.filter (independentCachedEdge 34)=independentCachedBranchMembers5991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5991
def independentCachedBranchMembers5993 : Finset ℕ := ([34,80,136,250,1590,1626,1692,1776,2606,2652,2714,2792,3130,3158,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5993 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5993 4 (fun x => (if x<2606 then (if x<1590 then (if x<136 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1692 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3214 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5994 : Finset ℕ := ([34,80,136,250,1590,1626,1642,1652,1692,1708,1714,1776,2606,2652,2668,2674,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5994 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5994 2668 4
  · have he : independentCachedBranchMembers5994.erase 2668=independentCachedBranchMembers5992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5992
  · have he : independentCachedBranchMembers5994.filter (independentCachedEdge 2668)=independentCachedBranchMembers5993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5993
def independentCachedBranchMembers5995 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5995 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5995 3270 5
  · have he : independentCachedBranchMembers5995.erase 3270=independentCachedBranchMembers5983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5983
  · have he : independentCachedBranchMembers5995.filter (independentCachedEdge 3270)=independentCachedBranchMembers5994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5994
def independentCachedBranchMembers5996 : Finset ℕ := ([130,238,1596,1614,1686,1702,1720,1738,1748,1764,2606,2652,2668,2674,2714,2730,2740,2758,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5996 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5996 5 (fun x => (if x<2674 then (if x<1720 then (if x<1614 then (if x<238 then 0 else (if x<1596 then 0 else 1)) else (if x<1686 then 1 else (if x<1702 then 1 else 0))) else (if x<1764 then (if x<1738 then 2 else (if x<1748 then 0 else 2)) else (if x<2652 then (if x<2606 then 1 else 3) else (if x<2668 then 3 else 1)))) else (if x<3158 then (if x<2740 then (if x<2714 then 3 else (if x<2730 then 3 else 0)) else (if x<2792 then (if x<2758 then 1 else 0) else (if x<3130 then 3 else 2))) else (if x<3214 then (if x<3174 then 2 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 0 else 4) else (if x<3298 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5997 : Finset ℕ := ([1596,1686,1702,1738,2606,2674,2740,2792,3192,3214,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5997 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5997 4 (fun x => (if x<2740 then (if x<1738 then (if x<1686 then 0 else (if x<1702 then 0 else 1)) else (if x<2606 then 1 else (if x<2674 then 2 else 2))) else (if x<3214 then (if x<2792 then 0 else (if x<3192 then 2 else 3)) else (if x<3282 then 1 else (if x<3298 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5998 : Finset ℕ := ([68,130,238,1596,1614,1686,1702,1720,1738,1748,1764,2606,2652,2668,2674,2714,2730,2740,2758,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5998 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5998 68 4
  · have he : independentCachedBranchMembers5998.erase 68=independentCachedBranchMembers5996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5996
  · have he : independentCachedBranchMembers5998.filter (independentCachedEdge 68)=independentCachedBranchMembers5997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5997
def independentCachedBranchMembers5999 : Finset ℕ := ([1614,1702,1738,1764,2652,2674,2714,2740,3174,3214,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5999 4 (fun x => (if x<2714 then (if x<1764 then (if x<1702 then 0 else (if x<1738 then 0 else 1)) else (if x<2652 then 1 else (if x<2674 then 0 else 2))) else (if x<3214 then (if x<2740 then 1 else (if x<3174 then 0 else 2)) else (if x<3276 then 2 else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6000 : Finset ℕ := ([40,68,130,238,1596,1614,1686,1702,1720,1738,1748,1764,2606,2652,2668,2674,2714,2730,2740,2758,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6000 40 4
  · have he : independentCachedBranchMembers6000.erase 40=independentCachedBranchMembers5998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5998
  · have he : independentCachedBranchMembers6000.filter (independentCachedEdge 40)=independentCachedBranchMembers5999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5999
def independentCachedBranchMembers6001 : Finset ℕ := ([40,68,130,238,1596,1614,1686,1764,2606,2652,2714,2792,3130,3158,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6001 4 (fun x => (if x<2606 then (if x<1596 then (if x<130 then (if x<68 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1686 then (if x<1614 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3130 then (if x<2714 then (if x<2652 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3214 then (if x<3158 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6002 : Finset ℕ := ([40,68,130,238,1596,1614,1686,1702,1720,1738,1748,1764,2606,2652,2668,2674,2714,2730,2740,2758,2776,2792,3130,3158,3174,3192,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6002 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6002 2776 4
  · have he : independentCachedBranchMembers6002.erase 2776=independentCachedBranchMembers6000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6000
  · have he : independentCachedBranchMembers6002.filter (independentCachedEdge 2776)=independentCachedBranchMembers6001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6001
def independentCachedBranchMembers6003 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6003 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6003 3186 5
  · have he : independentCachedBranchMembers6003.erase 3186=independentCachedBranchMembers5995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5995
  · have he : independentCachedBranchMembers6003.filter (independentCachedEdge 3186)=independentCachedBranchMembers6002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6002
def independentCachedBranchMembers6004 : Finset ℕ := ([136,250,1590,1626,1692,1702,1720,1738,1748,1776,2618,2646,2668,2674,2702,2730,2740,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6004 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6004 5 (fun x => (if x<2674 then (if x<1720 then (if x<1626 then (if x<250 then 0 else (if x<1590 then 0 else 1)) else (if x<1692 then 1 else (if x<1702 then 1 else 2))) else (if x<1776 then (if x<1738 then 0 else (if x<1748 then 0 else 2)) else (if x<2646 then (if x<2618 then 1 else 3) else (if x<2668 then 3 else 3)))) else (if x<3164 then (if x<2740 then (if x<2702 then 1 else (if x<2730 then 3 else 0)) else (if x<2786 then (if x<2776 then 1 else 0) else (if x<3118 then 3 else 2))) else (if x<3226 then (if x<3174 then 2 else (if x<3192 then 4 else 4)) else (if x<3282 then (if x<3276 then 0 else 4) else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6005 : Finset ℕ := ([1590,1692,1720,1738,2618,2668,2740,2786,3174,3226,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6005 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6005 4 (fun x => (if x<2740 then (if x<1738 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2618 then 1 else (if x<2668 then 2 else 2))) else (if x<3226 then (if x<2786 then 0 else (if x<3174 then 2 else 3)) else (if x<3276 then 1 else (if x<3304 then 3 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6006 : Finset ℕ := ([80,136,250,1590,1626,1692,1702,1720,1738,1748,1776,2618,2646,2668,2674,2702,2730,2740,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6006 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6006 80 4
  · have he : independentCachedBranchMembers6006.erase 80=independentCachedBranchMembers6004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6004
  · have he : independentCachedBranchMembers6006.filter (independentCachedEdge 80)=independentCachedBranchMembers6005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6005
def independentCachedBranchMembers6007 : Finset ℕ := ([1626,1720,1738,1776,2646,2668,2702,2740,3192,3226,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6007 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6007 4 (fun x => (if x<2702 then (if x<1776 then (if x<1720 then 0 else (if x<1738 then 0 else 1)) else (if x<2646 then 1 else (if x<2668 then 0 else 2))) else (if x<3226 then (if x<2740 then 1 else (if x<3192 then 0 else 2)) else (if x<3282 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6008 : Finset ℕ := ([34,80,136,250,1590,1626,1692,1702,1720,1738,1748,1776,2618,2646,2668,2674,2702,2730,2740,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6008 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6008 34 4
  · have he : independentCachedBranchMembers6008.erase 34=independentCachedBranchMembers6006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6006
  · have he : independentCachedBranchMembers6008.filter (independentCachedEdge 34)=independentCachedBranchMembers6007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6007
def independentCachedBranchMembers6009 : Finset ℕ := ([34,80,136,250,1590,1626,1692,1776,2618,2646,2702,2786,3118,3164,3226,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6009 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6009 4 (fun x => (if x<2618 then (if x<1590 then (if x<136 then (if x<80 then 0 else 0) else (if x<250 then 0 else 0)) else (if x<1692 then (if x<1626 then 1 else 1) else (if x<1776 then 1 else 1))) else (if x<3118 then (if x<2702 then (if x<2646 then 2 else 2) else (if x<2786 then 2 else 2)) else (if x<3226 then (if x<3164 then 3 else 3) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6010 : Finset ℕ := ([34,80,136,250,1590,1626,1692,1702,1720,1738,1748,1776,2618,2646,2668,2674,2702,2730,2740,2758,2776,2786,3118,3164,3174,3192,3226,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6010 2758 4
  · have he : independentCachedBranchMembers6010.erase 2758=independentCachedBranchMembers6008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6008
  · have he : independentCachedBranchMembers6010.filter (independentCachedEdge 2758)=independentCachedBranchMembers6009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6009
def independentCachedBranchMembers6011 : Finset ℕ := ([34,40,68,80,130,136,238,250,1590,1596,1614,1626,1642,1652,1686,1692,1702,1708,1714,1720,1738,1748,1764,1776,2606,2618,2646,2652,2668,2674,2702,2714,2730,2740,2758,2776,2786,2792,3118,3130,3158,3164,3174,3180,3186,3192,3214,3226,3242,3252,3270,3276,3282,3288,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6011 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6011 3180 5
  · have he : independentCachedBranchMembers6011.erase 3180=independentCachedBranchMembers6003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6003
  · have he : independentCachedBranchMembers6011.filter (independentCachedEdge 3180)=independentCachedBranchMembers6010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6010
def independentCachedBranchMembers6012 : Finset ℕ := ([130,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6012 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6012 5 (fun x => (if x<2674 then (if x<1708 then (if x<1642 then (if x<250 then 0 else 0) else (if x<1652 then 1 else (if x<1702 then 1 else 1))) else (if x<1738 then (if x<1714 then 2 else (if x<1720 then 0 else 1)) else (if x<1748 then 0 else (if x<2668 then 2 else 3)))) else (if x<3158 then (if x<2776 then (if x<2730 then 3 else (if x<2758 then 0 else 3)) else (if x<3118 then 3 else (if x<3130 then 2 else 4))) else (if x<3226 then (if x<3164 then 2 else (if x<3214 then 4 else 4)) else (if x<3298 then 0 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6013 : Finset ℕ := ([1642,1714,1720,1738,2668,2758,3130,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6013 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6013 4 (fun x => (if x<2758 then (if x<1720 then (if x<1714 then 0 else 0) else (if x<1738 then 1 else (if x<2668 then 1 else 0))) else (if x<3226 then (if x<3130 then 1 else 2) else (if x<3298 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers6014 : Finset ℕ := ([80,130,250,1642,1652,1702,1708,1714,1720,1738,1748,2668,2674,2730,2758,2776,3118,3130,3158,3164,3214,3226,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound6014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6014 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers6014 80 4
  · have he : independentCachedBranchMembers6014.erase 80=independentCachedBranchMembers6012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6012
  · have he : independentCachedBranchMembers6014.filter (independentCachedEdge 80)=independentCachedBranchMembers6013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound6013
def independentCachedBranchMembers6015 : Finset ℕ := ([1652,1702,1714,1738,2674,2776,3164,3214,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound6015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers6015 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers6015 4 (fun x => (if x<2776 then (if x<1714 then (if x<1702 then 0 else 0) else (if x<1738 then 1 else (if x<2674 then 1 else 2))) else (if x<3214 then (if x<3164 then 2 else 0) else (if x<3226 then 0 else (if x<3298 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
