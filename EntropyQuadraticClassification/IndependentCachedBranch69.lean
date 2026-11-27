/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch68
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4992 : Finset ℕ := ([1594,1614,1642,1708,1752,2614,2620,2662,2668,2702,2730,2772,2800,3118,3162,3188,3222,3228,3256,3276,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4992 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4992 5 (fun x => (if x<2772 then (if x<2614 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1708 then 1 else (if x<1752 then 0 else 0))) else (if x<2668 then (if x<2620 then 2 else (if x<2662 then 3 else 1)) else (if x<2702 then 2 else (if x<2730 then 2 else 1)))) else (if x<3222 then (if x<3118 then (if x<2800 then 2 else 3) else (if x<3162 then 0 else (if x<3188 then 0 else 2))) else (if x<3276 then (if x<3228 then 2 else (if x<3256 then 4 else 0)) else (if x<3298 then 0 else (if x<3304 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4993 : Finset ℕ := ([1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4993 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4993 1626 5
  · have he : independentCachedBranchMembers4993.erase 1626=independentCachedBranchMembers4991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4991
  · have he : independentCachedBranchMembers4993.filter (independentCachedEdge 1626)=independentCachedBranchMembers4992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4992
def independentCachedBranchMembers4994 : Finset ℕ := ([1594,1614,1642,1708,1752,2646,2652,2674,2680,2714,2740,2762,2788,3118,3162,3188,3222,3228,3256,3276,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4994 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4994 5 (fun x => (if x<2762 then (if x<2646 then (if x<1642 then (if x<1614 then 0 else 0) else (if x<1708 then 1 else (if x<1752 then 0 else 0))) else (if x<2680 then (if x<2652 then 2 else (if x<2674 then 3 else 1)) else (if x<2714 then 2 else (if x<2740 then 2 else 1)))) else (if x<3222 then (if x<3118 then (if x<2788 then 3 else 3) else (if x<3162 then 0 else (if x<3188 then 0 else 2))) else (if x<3276 then (if x<3228 then 2 else (if x<3256 then 1 else 0)) else (if x<3298 then 0 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4995 : Finset ℕ := ([1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4995 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4995 1582 5
  · have he : independentCachedBranchMembers4995.erase 1582=independentCachedBranchMembers4993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4993
  · have he : independentCachedBranchMembers4995.filter (independentCachedEdge 1582)=independentCachedBranchMembers4994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4994
def independentCachedBranchMembers4996 : Finset ℕ := ([1582,1614,1652,1686,1692,1708,1734,2614,2620,2646,2652,2662,2668,2702,2740,2772,2788,3118,3150,3188,3222,3228,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4996 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4996 5 (fun x => (if x<2668 then (if x<1734 then (if x<1686 then (if x<1614 then 0 else (if x<1652 then 1 else 0)) else (if x<1692 then 0 else (if x<1708 then 1 else 2))) else (if x<2646 then (if x<2614 then 2 else (if x<2620 then 0 else 2)) else (if x<2652 then 2 else (if x<2662 then 1 else 1)))) else (if x<3150 then (if x<2772 then (if x<2702 then 0 else (if x<2740 then 0 else 1)) else (if x<2788 then 0 else (if x<3118 then 2 else 3))) else (if x<3228 then (if x<3188 then 4 else (if x<3222 then 3 else 3)) else (if x<3238 then 4 else (if x<3276 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4997 : Finset ℕ := ([250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4997 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4997 250 5
  · have he : independentCachedBranchMembers4997.erase 250=independentCachedBranchMembers4995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4995
  · have he : independentCachedBranchMembers4997.filter (independentCachedEdge 250)=independentCachedBranchMembers4996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4996
def independentCachedBranchMembers4998 : Finset ℕ := ([1594,1626,1652,1708,1734,1762,1768,2614,2620,2646,2652,2674,2680,2702,2730,2762,2788,3130,3162,3188,3238,3276,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4998 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4998 5 (fun x => (if x<2680 then (if x<1768 then (if x<1708 then (if x<1626 then 0 else (if x<1652 then 1 else 0)) else (if x<1734 then 0 else (if x<1762 then 1 else 0))) else (if x<2646 then (if x<2614 then 1 else (if x<2620 then 2 else 0)) else (if x<2652 then 1 else (if x<2674 then 2 else 0)))) else (if x<3162 then (if x<2762 then (if x<2702 then 1 else (if x<2730 then 2 else 0)) else (if x<2788 then 1 else (if x<3130 then 0 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3238 then 2 else 2)) else (if x<3298 then 2 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4999 : Finset ℕ := ([144,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound4999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4999 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4999 144 5
  · have he : independentCachedBranchMembers4999.erase 144=independentCachedBranchMembers4997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4997
  · have he : independentCachedBranchMembers4999.filter (independentCachedEdge 144)=independentCachedBranchMembers4998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4998
def independentCachedBranchMembers5000 : Finset ℕ := ([1582,1594,1652,1686,1714,1752,1768,2614,2668,2680,2702,2714,2730,2772,2788,2800,3118,3130,3188,3222,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5000 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5000 5 (fun x => (if x<2714 then (if x<1752 then (if x<1652 then (if x<1594 then 0 else 1) else (if x<1686 then 0 else (if x<1714 then 0 else 2))) else (if x<2668 then (if x<1768 then 1 else (if x<2614 then 2 else 0)) else (if x<2680 then 0 else (if x<2702 then 1 else 0)))) else (if x<3130 then (if x<2788 then (if x<2730 then 1 else (if x<2772 then 2 else 0)) else (if x<2800 then 3 else (if x<3118 then 2 else 4))) else (if x<3238 then (if x<3188 then 3 else (if x<3222 then 3 else 4)) else (if x<3276 then 3 else (if x<3304 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5001 : Finset ℕ := ([1582,1594,1686,1768,2668,2680,2730,2772,3118,3130,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5001 4 (fun x => (if x<2730 then (if x<1768 then (if x<1594 then 0 else (if x<1686 then 1 else 0)) else (if x<2668 then 1 else (if x<2680 then 0 else 1))) else (if x<3130 then (if x<2772 then 1 else (if x<3118 then 0 else 2)) else (if x<3222 then 3 else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5002 : Finset ℕ := ([1582,1594,1652,1686,1714,1752,1768,2614,2652,2668,2680,2702,2714,2730,2772,2788,2800,3118,3130,3188,3222,3238,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5002 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5002 2652 4
  · have he : independentCachedBranchMembers5002.erase 2652=independentCachedBranchMembers5000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5000
  · have he : independentCachedBranchMembers5002.filter (independentCachedEdge 2652)=independentCachedBranchMembers5001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5001
def independentCachedBranchMembers5003 : Finset ℕ := ([66,144,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5003 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5003 66 5
  · have he : independentCachedBranchMembers5003.erase 66=independentCachedBranchMembers4999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4999
  · have he : independentCachedBranchMembers5003.filter (independentCachedEdge 66)=independentCachedBranchMembers5002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5002
def independentCachedBranchMembers5004 : Finset ℕ := ([1614,1626,1652,1692,1714,1752,1762,2652,2662,2674,2702,2714,2740,2762,2788,2800,3150,3162,3188,3228,3238,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5004 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5004 5 (fun x => (if x<2714 then (if x<1752 then (if x<1652 then (if x<1626 then 0 else 1) else (if x<1692 then 0 else (if x<1714 then 0 else 1))) else (if x<2662 then (if x<1762 then 2 else (if x<2652 then 2 else 0)) else (if x<2674 then 0 else (if x<2702 then 1 else 0)))) else (if x<3162 then (if x<2788 then (if x<2740 then 1 else (if x<2762 then 0 else 2)) else (if x<2800 then 3 else (if x<3150 then 2 else 4))) else (if x<3238 then (if x<3188 then 3 else (if x<3228 then 3 else 4)) else (if x<3276 then 4 else (if x<3298 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5005 : Finset ℕ := ([1614,1626,1692,1762,2662,2674,2740,2762,3150,3162,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5005 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5005 4 (fun x => (if x<2740 then (if x<1762 then (if x<1626 then 0 else (if x<1692 then 1 else 0)) else (if x<2662 then 1 else (if x<2674 then 0 else 1))) else (if x<3162 then (if x<2762 then 0 else (if x<3150 then 1 else 2)) else (if x<3228 then 3 else (if x<3298 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5006 : Finset ℕ := ([1614,1626,1652,1692,1714,1752,1762,2614,2652,2662,2674,2702,2714,2740,2762,2788,2800,3150,3162,3188,3228,3238,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5006 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5006 2614 4
  · have he : independentCachedBranchMembers5006.erase 2614=independentCachedBranchMembers5004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5004
  · have he : independentCachedBranchMembers5006.filter (independentCachedEdge 2614)=independentCachedBranchMembers5005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5005
def independentCachedBranchMembers5007 : Finset ℕ := ([40,66,144,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5007 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5007 40 5
  · have he : independentCachedBranchMembers5007.erase 40=independentCachedBranchMembers5003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5003
  · have he : independentCachedBranchMembers5007.filter (independentCachedEdge 40)=independentCachedBranchMembers5006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5006
def independentCachedBranchMembers5008 : Finset ℕ := ([1594,1626,1652,1686,1692,1714,1752,2614,2620,2646,2652,2674,2680,2714,2740,2772,2800,3130,3162,3188,3222,3228,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5008 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5008 5 (fun x => (if x<2680 then (if x<1752 then (if x<1686 then (if x<1626 then 0 else (if x<1652 then 1 else 0)) else (if x<1692 then 0 else (if x<1714 then 1 else 1))) else (if x<2646 then (if x<2614 then 0 else (if x<2620 then 0 else 2)) else (if x<2652 then 2 else (if x<2674 then 1 else 1)))) else (if x<3162 then (if x<2772 then (if x<2714 then 0 else (if x<2740 then 0 else 1)) else (if x<2800 then 0 else (if x<3130 then 2 else 3))) else (if x<3228 then (if x<3188 then 4 else (if x<3222 then 2 else 3)) else (if x<3256 then 4 else (if x<3282 then 2 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5009 : Finset ℕ := ([1652,1686,1692,2614,2620,2646,2652,2740,2772,3188,3222,3228] : List ℕ).toFinset
theorem independentCachedBranchBound5009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5009 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5009 4 (fun x => (if x<2652 then (if x<2614 then (if x<1686 then 0 else (if x<1692 then 0 else 1)) else (if x<2620 then 0 else (if x<2646 then 1 else 2))) else (if x<3188 then (if x<2740 then 3 else (if x<2772 then 2 else 0)) else (if x<3222 then 2 else (if x<3228 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5010 : Finset ℕ := ([250,1594,1626,1652,1686,1692,1714,1752,2614,2620,2646,2652,2674,2680,2714,2740,2772,2800,3130,3162,3188,3222,3228,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5010 250 4
  · have he : independentCachedBranchMembers5010.erase 250=independentCachedBranchMembers5008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5008
  · have he : independentCachedBranchMembers5010.filter (independentCachedEdge 250)=independentCachedBranchMembers5009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5009
def independentCachedBranchMembers5011 : Finset ℕ := ([1594,1626,1652,2614,2620,2646,2652,2674,2680,3130,3162,3188] : List ℕ).toFinset
theorem independentCachedBranchBound5011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5011 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5011 4 (fun x => (if x<2652 then (if x<2614 then (if x<1626 then 0 else (if x<1652 then 1 else 0)) else (if x<2620 then 0 else (if x<2646 then 2 else 1))) else (if x<3130 then (if x<2674 then 3 else (if x<2680 then 2 else 0)) else (if x<3162 then 2 else (if x<3188 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5012 : Finset ℕ := ([144,250,1594,1626,1652,1686,1692,1714,1752,2614,2620,2646,2652,2674,2680,2714,2740,2772,2800,3130,3162,3188,3222,3228,3256,3282] : List ℕ).toFinset
theorem independentCachedBranchBound5012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5012 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5012 144 4
  · have he : independentCachedBranchMembers5012.erase 144=independentCachedBranchMembers5010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5010
  · have he : independentCachedBranchMembers5012.filter (independentCachedEdge 144)=independentCachedBranchMembers5011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5011
def independentCachedBranchMembers5013 : Finset ℕ := ([40,66,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5013 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5013 238 5
  · have he : independentCachedBranchMembers5013.erase 238=independentCachedBranchMembers5007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5007
  · have he : independentCachedBranchMembers5013.filter (independentCachedEdge 238)=independentCachedBranchMembers5012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5012
def independentCachedBranchMembers5014 : Finset ℕ := ([1582,1614,1652,1714,1752,1762,1768,2614,2620,2646,2652,2662,2668,2714,2730,2762,2800,3118,3150,3188,3256,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5014 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5014 5 (fun x => (if x<2668 then (if x<1768 then (if x<1714 then (if x<1614 then 0 else (if x<1652 then 1 else 0)) else (if x<1752 then 0 else (if x<1762 then 1 else 1))) else (if x<2646 then (if x<2614 then 0 else (if x<2620 then 0 else 2)) else (if x<2652 then 2 else (if x<2662 then 1 else 1)))) else (if x<3150 then (if x<2762 then (if x<2714 then 0 else (if x<2730 then 2 else 0)) else (if x<2800 then 1 else (if x<3118 then 0 else 3))) else (if x<3282 then (if x<3188 then 4 else (if x<3256 then 2 else 2)) else (if x<3298 then 2 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5015 : Finset ℕ := ([1582,1614,1652,2614,2620,2646,2652,2662,2668,3118,3150,3188] : List ℕ).toFinset
theorem independentCachedBranchBound5015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5015 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5015 4 (fun x => (if x<2652 then (if x<2614 then (if x<1614 then 0 else (if x<1652 then 1 else 0)) else (if x<2620 then 0 else (if x<2646 then 2 else 1))) else (if x<3118 then (if x<2662 then 3 else (if x<2668 then 2 else 0)) else (if x<3150 then 2 else (if x<3188 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5016 : Finset ℕ := ([250,1582,1614,1652,1714,1752,1762,1768,2614,2620,2646,2652,2662,2668,2714,2730,2762,2800,3118,3150,3188,3256,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5016 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5016 250 4
  · have he : independentCachedBranchMembers5016.erase 250=independentCachedBranchMembers5014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5014
  · have he : independentCachedBranchMembers5016.filter (independentCachedEdge 250)=independentCachedBranchMembers5015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5015
def independentCachedBranchMembers5017 : Finset ℕ := ([1652,1762,1768,2614,2620,2646,2652,2730,2762,3188,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5017 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5017 4 (fun x => (if x<2652 then (if x<2614 then (if x<1762 then 0 else (if x<1768 then 0 else 1)) else (if x<2620 then 1 else (if x<2646 then 0 else 2))) else (if x<3188 then (if x<2730 then 3 else (if x<2762 then 0 else 2)) else (if x<3298 then 2 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5018 : Finset ℕ := ([144,250,1582,1614,1652,1714,1752,1762,1768,2614,2620,2646,2652,2662,2668,2714,2730,2762,2800,3118,3150,3188,3256,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5018 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5018 144 4
  · have he : independentCachedBranchMembers5018.erase 144=independentCachedBranchMembers5016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5016
  · have he : independentCachedBranchMembers5018.filter (independentCachedEdge 144)=independentCachedBranchMembers5017 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5017
def independentCachedBranchMembers5019 : Finset ℕ := ([40,66,132,144,238,250,1582,1594,1614,1626,1642,1652,1686,1692,1708,1714,1734,1752,1762,1768,2614,2620,2646,2652,2662,2668,2674,2680,2702,2714,2730,2740,2762,2772,2788,2800,3118,3130,3150,3162,3178,3188,3222,3228,3238,3256,3276,3282,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound5019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5019 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5019 132 5
  · have he : independentCachedBranchMembers5019.erase 132=independentCachedBranchMembers5013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5013
  · have he : independentCachedBranchMembers5019.filter (independentCachedEdge 132)=independentCachedBranchMembers5018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5018
def independentCachedBranchMembers5020 : Finset ℕ := ([1582,1594,1652,1692,1708,1734,1762,2620,2646,2662,2674,2702,2714,2730,2772,2788,2800,3118,3130,3188,3228,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5020 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5020 5 (fun x => (if x<2714 then (if x<1762 then (if x<1692 then (if x<1594 then 0 else (if x<1652 then 1 else 0)) else (if x<1708 then 0 else (if x<1734 then 1 else 0))) else (if x<2662 then (if x<2620 then 1 else (if x<2646 then 0 else 2)) else (if x<2674 then 0 else (if x<2702 then 1 else 0)))) else (if x<3130 then (if x<2788 then (if x<2730 then 2 else (if x<2772 then 1 else 0)) else (if x<2800 then 1 else (if x<3118 then 2 else 3))) else (if x<3256 then (if x<3188 then 4 else (if x<3228 then 2 else 3)) else (if x<3282 then 2 else (if x<3298 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5021 : Finset ℕ := ([1582,1594,1652,2702,2714,2730,2772,2788,2800,3118,3130,3188] : List ℕ).toFinset
theorem independentCachedBranchBound5021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5021 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5021 4 (fun x => (if x<2772 then (if x<2702 then (if x<1594 then 0 else (if x<1652 then 1 else 0)) else (if x<2714 then 0 else (if x<2730 then 1 else 2))) else (if x<3118 then (if x<2788 then 0 else (if x<2800 then 2 else 3)) else (if x<3130 then 3 else (if x<3188 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers5022 : Finset ℕ := ([66,1582,1594,1652,1692,1708,1734,1762,2620,2646,2662,2674,2702,2714,2730,2772,2788,2800,3118,3130,3188,3228,3256,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers5022 66 4
  · have he : independentCachedBranchMembers5022.erase 66=independentCachedBranchMembers5020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5020
  · have he : independentCachedBranchMembers5022.filter (independentCachedEdge 66)=independentCachedBranchMembers5021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound5021
def independentCachedBranchMembers5023 : Finset ℕ := ([1652,1762,2662,2674,2702,2714,2788,2800,3188,3228,3298] : List ℕ).toFinset
theorem independentCachedBranchBound5023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers5023 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers5023 4 (fun x => (if x<2714 then (if x<2662 then (if x<1762 then 0 else 0) else (if x<2674 then 0 else (if x<2702 then 1 else 2))) else (if x<3188 then (if x<2788 then 1 else (if x<2800 then 2 else 0)) else (if x<3228 then 1 else (if x<3298 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
