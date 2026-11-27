/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch231
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10208 : Finset ℕ := ([238,1678,1706,1738,2676,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10208 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10208 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10208 3 (fun x => (if x<1738 then (if x<1678 then 0 else (if x<1706 then 0 else 1)) else (if x<2676 then 2 else (if x<3188 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10209 : Finset ℕ := ([144,238,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,3118,3150,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10209 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10209 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10209 144 3
  · have he : independentCachedBranchMembers10209.erase 144=independentCachedBranchMembers10207 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10207
  · have he : independentCachedBranchMembers10209.filter (independentCachedEdge 144)=independentCachedBranchMembers10208 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10208
def independentCachedBranchMembers10210 : Finset ℕ := ([18,40,72,144,238,1590,1622,1644,1650,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2732,2738,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10210 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10210 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10210 18 4
  · have he : independentCachedBranchMembers10210.erase 18=independentCachedBranchMembers10206 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10206
  · have he : independentCachedBranchMembers10210.filter (independentCachedEdge 18)=independentCachedBranchMembers10209 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10209
def independentCachedBranchMembers10211 : Finset ℕ := ([40,72,1590,1622,1706,1716,1738,1748,2666,2676,2710,2792,3178,3188,3222,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10211 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10211 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10211 4 (fun x => (if x<2666 then (if x<1706 then (if x<1590 then (if x<72 then 0 else 1) else (if x<1622 then 1 else 0)) else (if x<1738 then (if x<1716 then 2 else 2) else (if x<1748 then 3 else 3))) else (if x<3178 then (if x<2710 then (if x<2676 then 2 else 2) else (if x<2792 then 0 else 1)) else (if x<3222 then (if x<3188 then 3 else 3) else (if x<3304 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10212 : Finset ℕ := ([12,18,40,72,144,238,1590,1622,1644,1650,1678,1706,1716,1738,1748,1776,2606,2638,2666,2676,2710,2732,2738,2764,2770,2792,3118,3150,3178,3188,3222,3244,3250,3276,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound10212 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10212 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10212 12 4
  · have he : independentCachedBranchMembers10212.erase 12=independentCachedBranchMembers10210 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10210
  · have he : independentCachedBranchMembers10212.filter (independentCachedEdge 12)=independentCachedBranchMembers10211 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10211
def independentCachedBranchMembers10213 : Finset ℕ := ([12,18,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1644,1650,1652,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10213 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10213 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10213 1652 5
  · have he : independentCachedBranchMembers10213.erase 1652=independentCachedBranchMembers10187 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10187
  · have he : independentCachedBranchMembers10213.filter (independentCachedEdge 1652)=independentCachedBranchMembers10212 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10212
def independentCachedBranchMembers10214 : Finset ℕ := ([80,246,1582,1614,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10214 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10214 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10214 5 (fun x => (if x<2666 then (if x<1706 then (if x<1614 then (if x<246 then 0 else (if x<1582 then 0 else 1)) else (if x<1650 then 2 else (if x<1686 then 0 else 1))) else (if x<1748 then (if x<1716 then 2 else (if x<1738 then 3 else 1)) else (if x<2614 then (if x<1768 then 0 else 3) else (if x<2646 then 1 else 0)))) else (if x<3158 then (if x<2764 then (if x<2676 then 1 else (if x<2702 then 4 else 1)) else (if x<2800 then (if x<2770 then 4 else 1) else (if x<3126 then 0 else 3))) else (if x<3214 then (if x<3178 then 2 else (if x<3188 then 2 else 0)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10215 : Finset ℕ := ([246,1582,1614,1686,1716,1748,2666,2770,2800,3178,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10215 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10215 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10215 4 (fun x => (if x<2666 then (if x<1686 then (if x<1582 then 0 else (if x<1614 then 1 else 2)) else (if x<1716 then 0 else (if x<1748 then 1 else 2))) else (if x<3178 then (if x<2770 then 1 else (if x<2800 then 0 else 1)) else (if x<3250 then 2 else (if x<3312 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10216 : Finset ℕ := ([80,136,246,1582,1614,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10216 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10216 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10216 136 4
  · have he : independentCachedBranchMembers10216.erase 136=independentCachedBranchMembers10214 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10214
  · have he : independentCachedBranchMembers10216.filter (independentCachedEdge 136)=independentCachedBranchMembers10215 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10215
def independentCachedBranchMembers10217 : Finset ℕ := ([80,1582,1686,1706,1748,1768,2646,2666,2770,3158,3178,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10217 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10217 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10217 4 (fun x => (if x<2646 then (if x<1706 then (if x<1582 then 0 else (if x<1686 then 0 else 1)) else (if x<1748 then 1 else (if x<1768 then 2 else 2))) else (if x<3158 then (if x<2666 then 1 else (if x<2770 then 1 else 0)) else (if x<3178 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10218 : Finset ℕ := ([48,80,136,246,1582,1614,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10218 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10218 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10218 48 4
  · have he : independentCachedBranchMembers10218.erase 48=independentCachedBranchMembers10216 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10216
  · have he : independentCachedBranchMembers10218.filter (independentCachedEdge 48)=independentCachedBranchMembers10217 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10217
def independentCachedBranchMembers10219 : Finset ℕ := ([136,1614,1706,1716,1768,2614,2666,2676,2702,2764,2770,3158,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10219 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10219 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10219 4 (fun x => (if x<2676 then (if x<1716 then (if x<1614 then 0 else (if x<1706 then 1 else 0)) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2666 then 2 else 1))) else (if x<3158 then (if x<2764 then (if x<2702 then 0 else 3) else (if x<2770 then 1 else 3)) else (if x<3250 then (if x<3244 then 0 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10220 : Finset ℕ := ([1706,1768,2666,2770,3158,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10220 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10220 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10220 3 (fun x => (if x<2770 then (if x<1768 then 0 else (if x<2666 then 1 else 0)) else (if x<3158 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10221 : Finset ℕ := ([48,136,1614,1706,1716,1768,2614,2666,2676,2702,2764,2770,3158,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10221 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10221 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10221 48 3
  · have he : independentCachedBranchMembers10221.erase 48=independentCachedBranchMembers10219 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10219
  · have he : independentCachedBranchMembers10221.filter (independentCachedEdge 48)=independentCachedBranchMembers10220 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10220
def independentCachedBranchMembers10222 : Finset ℕ := ([48,80,136,246,1582,1614,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10222 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10222 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10222 3282 4
  · have he : independentCachedBranchMembers10222.erase 3282=independentCachedBranchMembers10218 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10218
  · have he : independentCachedBranchMembers10222.filter (independentCachedEdge 3282)=independentCachedBranchMembers10221 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10221
def independentCachedBranchMembers10223 : Finset ℕ := ([246,1582,1686,1706,1716,2646,2666,2676,2764,2770,2800,3126,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10223 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10223 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10223 4 (fun x => (if x<2676 then (if x<1706 then (if x<1582 then 0 else (if x<1686 then 1 else 0)) else (if x<2646 then (if x<1716 then 2 else 1) else (if x<2666 then 0 else 1))) else (if x<3126 then (if x<2770 then (if x<2764 then 2 else 3) else (if x<2800 then 3 else 1)) else (if x<3244 then (if x<3214 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10224 : Finset ℕ := ([1686,1716,2666,2764,3126,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10224 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10224 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10224 3 (fun x => (if x<2764 then (if x<1716 then 0 else (if x<2666 then 1 else 0)) else (if x<3126 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10225 : Finset ℕ := ([80,246,1582,1686,1706,1716,2646,2666,2676,2764,2770,2800,3126,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10225 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10225 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10225 80 3
  · have he : independentCachedBranchMembers10225.erase 80=independentCachedBranchMembers10223 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10223
  · have he : independentCachedBranchMembers10225.filter (independentCachedEdge 80)=independentCachedBranchMembers10224 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10224
def independentCachedBranchMembers10226 : Finset ℕ := ([48,80,136,246,1582,1614,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10226 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10226 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10226 3276 4
  · have he : independentCachedBranchMembers10226.erase 3276=independentCachedBranchMembers10222 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10222
  · have he : independentCachedBranchMembers10226.filter (independentCachedEdge 3276)=independentCachedBranchMembers10225 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10225
def independentCachedBranchMembers10227 : Finset ℕ := ([80,136,1582,1738,1748,1768,2614,2764,2770,2800,3158,3178,3188,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10227 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10227 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10227 4 (fun x => (if x<2770 then (if x<1748 then (if x<1582 then (if x<136 then 0 else 0) else (if x<1738 then 1 else 1)) else (if x<2614 then (if x<1768 then 2 else 2) else (if x<2764 then 1 else 2))) else (if x<3188 then (if x<3158 then (if x<2800 then 1 else 2) else (if x<3178 then 0 else 3)) else (if x<3244 then (if x<3214 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10228 : Finset ℕ := ([48,80,136,246,1582,1614,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2738,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10228 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10228 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10228 2738 4
  · have he : independentCachedBranchMembers10228.erase 2738=independentCachedBranchMembers10226 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10226
  · have he : independentCachedBranchMembers10228.filter (independentCachedEdge 2738)=independentCachedBranchMembers10227 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10227
def independentCachedBranchMembers10229 : Finset ℕ := ([48,246,1614,1686,1738,1748,2646,2702,2764,2770,3126,3178,3188,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10229 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10229 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10229 4 (fun x => (if x<2764 then (if x<1738 then (if x<1614 then (if x<246 then 0 else 0) else (if x<1686 then 1 else 1)) else (if x<2646 then (if x<1748 then 2 else 2) else (if x<2702 then 1 else 1))) else (if x<3188 then (if x<3126 then (if x<2770 then 2 else 2) else (if x<3178 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10230 : Finset ℕ := ([48,80,136,246,1582,1614,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2732,2738,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10230 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10230 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10230 2732 4
  · have he : independentCachedBranchMembers10230.erase 2732=independentCachedBranchMembers10228 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10228
  · have he : independentCachedBranchMembers10230.filter (independentCachedEdge 2732)=independentCachedBranchMembers10229 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10229
def independentCachedBranchMembers10231 : Finset ℕ := ([48,80,136,246,1582,1614,1686,1768,2614,2646,2702,2800,3126,3158,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10231 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10231 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10231 4 (fun x => (if x<2614 then (if x<1582 then (if x<136 then (if x<80 then 0 else 1) else (if x<246 then 0 else 1)) else (if x<1686 then (if x<1614 then 2 else 3) else (if x<1768 then 2 else 3))) else (if x<3126 then (if x<2702 then (if x<2646 then 0 else 1) else (if x<2800 then 0 else 1)) else (if x<3214 then (if x<3158 then 2 else 3) else (if x<3312 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10232 : Finset ℕ := ([48,80,136,246,1582,1614,1644,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2732,2738,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10232 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10232 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10232 1644 4
  · have he : independentCachedBranchMembers10232.erase 1644=independentCachedBranchMembers10230 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10230
  · have he : independentCachedBranchMembers10232.filter (independentCachedEdge 1644)=independentCachedBranchMembers10231 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10231
def independentCachedBranchMembers10233 : Finset ℕ := ([48,80,1582,1614,1706,1716,1738,1748,2666,2676,2702,2800,3178,3188,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10233 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10233 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10233 4 (fun x => (if x<2666 then (if x<1706 then (if x<1582 then (if x<80 then 0 else 1) else (if x<1614 then 1 else 0)) else (if x<1738 then (if x<1716 then 2 else 2) else (if x<1748 then 3 else 3))) else (if x<3178 then (if x<2702 then (if x<2676 then 2 else 2) else (if x<2800 then 0 else 1)) else (if x<3214 then (if x<3188 then 3 else 3) else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10234 : Finset ℕ := ([18,48,80,136,246,1582,1614,1644,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2732,2738,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10234 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10234 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10234 18 4
  · have he : independentCachedBranchMembers10234.erase 18=independentCachedBranchMembers10232 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10232
  · have he : independentCachedBranchMembers10234.filter (independentCachedEdge 18)=independentCachedBranchMembers10233 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10233
def independentCachedBranchMembers10235 : Finset ℕ := ([246,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,3126,3158,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10235 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10235 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10235 4 (fun x => (if x<2614 then (if x<1716 then (if x<1686 then 0 else (if x<1706 then 0 else 1)) else (if x<1748 then (if x<1738 then 1 else 2) else (if x<1768 then 2 else 3))) else (if x<3126 then (if x<2666 then (if x<2646 then 0 else 3) else (if x<2676 then 1 else 1)) else (if x<3178 then (if x<3158 then 3 else 0) else (if x<3188 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10236 : Finset ℕ := ([246,1686,1716,1748,2666,3178] : List ℕ).toFinset
theorem independentCachedBranchBound10236 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10236 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10236 3 (fun x => (if x<1748 then (if x<1686 then 0 else (if x<1716 then 0 else 1)) else (if x<2666 then 2 else (if x<3178 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10237 : Finset ℕ := ([136,246,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,3126,3158,3178,3188] : List ℕ).toFinset
theorem independentCachedBranchBound10237 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10237 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10237 136 3
  · have he : independentCachedBranchMembers10237.erase 136=independentCachedBranchMembers10235 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10235
  · have he : independentCachedBranchMembers10237.filter (independentCachedEdge 136)=independentCachedBranchMembers10236 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10236
def independentCachedBranchMembers10238 : Finset ℕ := ([12,18,48,80,136,246,1582,1614,1644,1650,1686,1706,1716,1738,1748,1768,2614,2646,2666,2676,2702,2732,2738,2764,2770,2800,3126,3158,3178,3188,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10238 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10238 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10238 12 4
  · have he : independentCachedBranchMembers10238.erase 12=independentCachedBranchMembers10234 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10234
  · have he : independentCachedBranchMembers10238.filter (independentCachedEdge 12)=independentCachedBranchMembers10237 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10237
def independentCachedBranchMembers10239 : Finset ℕ := ([12,18,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1642,1644,1650,1652,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10239 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10239 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10239 1642 5
  · have he : independentCachedBranchMembers10239.erase 1642=independentCachedBranchMembers10213 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10213
  · have he : independentCachedBranchMembers10239.filter (independentCachedEdge 1642)=independentCachedBranchMembers10238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10238
end EntropyDesigns.QuadraticRefinement
