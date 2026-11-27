/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch232
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers10240 : Finset ℕ := ([12,144,238,1582,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10240 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10240 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10240 5 (fun x => (if x<2668 then (if x<1714 then (if x<1582 then (if x<144 then 0 else (if x<238 then 0 else 1)) else (if x<1678 then 0 else (if x<1708 then 1 else 2))) else (if x<1776 then (if x<1740 then 0 else (if x<1746 then 3 else 3)) else (if x<2606 then 2 else (if x<2638 then 1 else 0)))) else (if x<3150 then (if x<2770 then (if x<2674 then 3 else (if x<2764 then 2 else 1)) else (if x<2800 then 0 else (if x<3118 then 4 else 4))) else (if x<3214 then (if x<3180 then 1 else (if x<3186 then 0 else 4)) else (if x<3244 then 2 else (if x<3250 then 1 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10241 : Finset ℕ := ([144,238,1714,1740,2638,2668,2764,3150,3180,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10241 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10241 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10241 4 (fun x => (if x<2668 then (if x<1714 then (if x<238 then 0 else 1) else (if x<1740 then 0 else (if x<2638 then 1 else 0))) else (if x<3150 then (if x<2764 then 1 else 2) else (if x<3180 then 1 else (if x<3250 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10242 : Finset ℕ := ([12,80,144,238,1582,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10242 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10242 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10242 80 4
  · have he : independentCachedBranchMembers10242.erase 80=independentCachedBranchMembers10240 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10240
  · have he : independentCachedBranchMembers10242.filter (independentCachedEdge 80)=independentCachedBranchMembers10241 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10241
def independentCachedBranchMembers10243 : Finset ℕ := ([238,1708,1740,1776,2668,2764,2800,3118,3150,3186,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10243 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10243 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10243 4 (fun x => (if x<2800 then (if x<1776 then (if x<1708 then 0 else (if x<1740 then 0 else 1)) else (if x<2668 then 1 else (if x<2764 then 0 else 2))) else (if x<3186 then (if x<3118 then 2 else (if x<3150 then 0 else 1)) else (if x<3214 then 1 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10244 : Finset ℕ := ([12,80,144,238,1582,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10244 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10244 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10244 3312 4
  · have he : independentCachedBranchMembers10244.erase 3312=independentCachedBranchMembers10242 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10242
  · have he : independentCachedBranchMembers10244.filter (independentCachedEdge 3312)=independentCachedBranchMembers10243 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10243
def independentCachedBranchMembers10245 : Finset ℕ := ([144,1678,1714,1746,2606,2638,2674,2764,2800,3180,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10245 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10245 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10245 4 (fun x => (if x<2674 then (if x<1746 then (if x<1678 then 0 else (if x<1714 then 1 else 0)) else (if x<2606 then 1 else (if x<2638 then 1 else 0))) else (if x<3180 then (if x<2764 then 1 else (if x<2800 then 2 else 2)) else (if x<3214 then 0 else (if x<3250 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10246 : Finset ℕ := ([12,80,144,238,1582,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10246 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10246 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10246 2702 4
  · have he : independentCachedBranchMembers10246.erase 2702=independentCachedBranchMembers10244 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10244
  · have he : independentCachedBranchMembers10246.filter (independentCachedEdge 2702)=independentCachedBranchMembers10245 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10245
def independentCachedBranchMembers10247 : Finset ℕ := ([80,1582,1678,1714,1740,1776,2638,2674,2770,3150,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10247 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10247 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10247 4 (fun x => (if x<2638 then (if x<1714 then (if x<1582 then 0 else (if x<1678 then 0 else 1)) else (if x<1740 then 1 else (if x<1776 then 2 else 2))) else (if x<3150 then (if x<2674 then 1 else (if x<2770 then 1 else 0)) else (if x<3186 then 2 else (if x<3244 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10248 : Finset ℕ := ([12,80,144,238,1582,1614,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10248 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10248 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10248 1614 4
  · have he : independentCachedBranchMembers10248.erase 1614=independentCachedBranchMembers10246 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10246
  · have he : independentCachedBranchMembers10248.filter (independentCachedEdge 1614)=independentCachedBranchMembers10247 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10247
def independentCachedBranchMembers10249 : Finset ℕ := ([80,144,238,1582,1708,1746,2606,2668,2770,3118,3180,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10249 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10249 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10249 4 (fun x => (if x<2606 then (if x<1582 then (if x<144 then 0 else (if x<238 then 1 else 2)) else (if x<1708 then 0 else (if x<1746 then 2 else 1))) else (if x<3118 then (if x<2668 then 1 else (if x<2770 then 2 else 0)) else (if x<3180 then 2 else (if x<3244 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10250 : Finset ℕ := ([12,48,80,144,238,1582,1614,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10250 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10250 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10250 48 4
  · have he : independentCachedBranchMembers10250.erase 48=independentCachedBranchMembers10248 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10248
  · have he : independentCachedBranchMembers10250.filter (independentCachedEdge 48)=independentCachedBranchMembers10249 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10249
def independentCachedBranchMembers10251 : Finset ℕ := ([48,238,1614,1678,1740,1746,2638,2702,2764,2770,3118,3180,3186,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10251 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10251 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10251 4 (fun x => (if x<2764 then (if x<1740 then (if x<1614 then (if x<238 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<2638 then (if x<1746 then 2 else 2) else (if x<2702 then 1 else 0))) else (if x<3186 then (if x<3118 then (if x<2770 then 3 else 3) else (if x<3180 then 1 else 2)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10252 : Finset ℕ := ([12,48,80,144,238,1582,1614,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10252 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10252 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10252 3282 4
  · have he : independentCachedBranchMembers10252.erase 3282=independentCachedBranchMembers10250 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10250
  · have he : independentCachedBranchMembers10252.filter (independentCachedEdge 3282)=independentCachedBranchMembers10251 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10251
def independentCachedBranchMembers10253 : Finset ℕ := ([80,144,1582,1740,1746,1776,2606,2764,2770,2800,3150,3180,3186,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10253 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10253 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10253 4 (fun x => (if x<2770 then (if x<1746 then (if x<1582 then (if x<144 then 0 else 1) else (if x<1740 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2764 then 1 else 3))) else (if x<3186 then (if x<3150 then (if x<2800 then 0 else 3) else (if x<3180 then 2 else 1)) else (if x<3244 then (if x<3214 then 2 else 3) else (if x<3250 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10254 : Finset ℕ := ([12,48,80,144,238,1582,1614,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10254 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10254 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10254 3276 4
  · have he : independentCachedBranchMembers10254.erase 3276=independentCachedBranchMembers10252 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10252
  · have he : independentCachedBranchMembers10254.filter (independentCachedEdge 3276)=independentCachedBranchMembers10253 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10253
def independentCachedBranchMembers10255 : Finset ℕ := ([80,238,1582,1678,1708,1714,2638,2668,2674,2764,2770,2800,3118,3214,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10255 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10255 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10255 4 (fun x => (if x<2674 then (if x<1708 then (if x<1582 then (if x<238 then 0 else 1) else (if x<1678 then 0 else 1)) else (if x<2638 then (if x<1714 then 2 else 2) else (if x<2668 then 1 else 2))) else (if x<3118 then (if x<2770 then (if x<2764 then 2 else 3) else (if x<2800 then 0 else 3)) else (if x<3244 then (if x<3214 then 1 else 3) else (if x<3250 then 0 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10256 : Finset ℕ := ([12,48,80,144,238,1582,1614,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2738,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10256 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10256 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10256 2738 4
  · have he : independentCachedBranchMembers10256.erase 2738=independentCachedBranchMembers10254 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10254
  · have he : independentCachedBranchMembers10256.filter (independentCachedEdge 2738)=independentCachedBranchMembers10255 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10255
def independentCachedBranchMembers10257 : Finset ℕ := ([48,144,1614,1708,1714,1776,2606,2668,2674,2702,2764,2770,3150,3244,3250,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10257 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10257 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10257 4 (fun x => (if x<2674 then (if x<1714 then (if x<1614 then (if x<144 then 0 else 1) else (if x<1708 then 0 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2668 then 2 else 1))) else (if x<3150 then (if x<2764 then (if x<2702 then 2 else 0) else (if x<2770 then 3 else 3)) else (if x<3250 then (if x<3244 then 1 else 3) else (if x<3312 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10258 : Finset ℕ := ([12,48,80,144,238,1582,1614,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2732,2738,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10258 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10258 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10258 2732 4
  · have he : independentCachedBranchMembers10258.erase 2732=independentCachedBranchMembers10256 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10256
  · have he : independentCachedBranchMembers10258.filter (independentCachedEdge 2732)=independentCachedBranchMembers10257 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10257
def independentCachedBranchMembers10259 : Finset ℕ := ([238,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,3118,3150,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10259 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10259 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10259 4 (fun x => (if x<2606 then (if x<1714 then (if x<1678 then 0 else (if x<1708 then 0 else 1)) else (if x<1746 then (if x<1740 then 1 else 2) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2668 then (if x<2638 then 0 else 3) else (if x<2674 then 1 else 1)) else (if x<3180 then (if x<3150 then 3 else 0) else (if x<3186 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10260 : Finset ℕ := ([238,1678,1708,1740,2674,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10260 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10260 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10260 3 (fun x => (if x<1740 then (if x<1678 then 0 else (if x<1708 then 0 else 1)) else (if x<2674 then 2 else (if x<3186 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10261 : Finset ℕ := ([144,238,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,3118,3150,3180,3186] : List ℕ).toFinset
theorem independentCachedBranchBound10261 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10261 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10261 144 3
  · have he : independentCachedBranchMembers10261.erase 144=independentCachedBranchMembers10259 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10259
  · have he : independentCachedBranchMembers10261.filter (independentCachedEdge 144)=independentCachedBranchMembers10260 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10260
def independentCachedBranchMembers10262 : Finset ℕ := ([12,48,80,144,238,1582,1614,1650,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2732,2738,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10262 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10262 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10262 1650 4
  · have he : independentCachedBranchMembers10262.erase 1650=independentCachedBranchMembers10258 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10258
  · have he : independentCachedBranchMembers10262.filter (independentCachedEdge 1650)=independentCachedBranchMembers10261 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10261
def independentCachedBranchMembers10263 : Finset ℕ := ([48,80,1582,1614,1708,1714,1740,1746,2668,2674,2702,2800,3180,3186,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10263 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10263 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10263 4 (fun x => (if x<2668 then (if x<1708 then (if x<1582 then (if x<80 then 0 else 1) else (if x<1614 then 1 else 0)) else (if x<1740 then (if x<1714 then 2 else 2) else (if x<1746 then 3 else 3))) else (if x<3180 then (if x<2702 then (if x<2674 then 2 else 2) else (if x<2800 then 0 else 1)) else (if x<3214 then (if x<3186 then 3 else 3) else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10264 : Finset ℕ := ([12,48,80,144,238,1582,1614,1644,1650,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2732,2738,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10264 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10264 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10264 1644 4
  · have he : independentCachedBranchMembers10264.erase 1644=independentCachedBranchMembers10262 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10262
  · have he : independentCachedBranchMembers10264.filter (independentCachedEdge 1644)=independentCachedBranchMembers10263 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10263
def independentCachedBranchMembers10265 : Finset ℕ := ([48,80,144,238,1582,1614,1678,1776,2606,2638,2702,2800,3118,3150,3214,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10265 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10265 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10265 4 (fun x => (if x<2606 then (if x<1582 then (if x<144 then (if x<80 then 0 else 1) else (if x<238 then 2 else 3)) else (if x<1678 then (if x<1614 then 1 else 0) else (if x<1776 then 3 else 2))) else (if x<3118 then (if x<2702 then (if x<2638 then 2 else 3) else (if x<2800 then 0 else 1)) else (if x<3214 then (if x<3150 then 3 else 2) else (if x<3312 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10266 : Finset ℕ := ([12,18,48,80,144,238,1582,1614,1644,1650,1678,1708,1714,1740,1746,1776,2606,2638,2668,2674,2702,2732,2738,2764,2770,2800,3118,3150,3180,3186,3214,3244,3250,3276,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10266 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10266 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10266 18 4
  · have he : independentCachedBranchMembers10266.erase 18=independentCachedBranchMembers10264 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10264
  · have he : independentCachedBranchMembers10266.filter (independentCachedEdge 18)=independentCachedBranchMembers10265 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10265
def independentCachedBranchMembers10267 : Finset ℕ := ([12,18,20,40,48,72,80,136,144,238,246,1582,1590,1614,1622,1642,1644,1650,1652,1678,1686,1706,1708,1714,1716,1738,1740,1746,1748,1768,1776,2606,2614,2638,2646,2666,2668,2674,2676,2702,2710,2730,2732,2738,2740,2762,2764,2770,2772,2792,2800,3118,3126,3150,3158,3178,3180,3186,3188,3214,3222,3242,3244,3250,3252,3274,3276,3282,3284,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound10267 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10267 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10267 20 5
  · have he : independentCachedBranchMembers10267.erase 20=independentCachedBranchMembers10239 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10239
  · have he : independentCachedBranchMembers10267.filter (independentCachedEdge 20)=independentCachedBranchMembers10266 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10266
def independentCachedBranchMembers10268 : Finset ℕ := ([18,136,246,1590,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10268 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10268 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10268 5 (fun x => (if x<2668 then (if x<1714 then (if x<1590 then (if x<136 then 0 else (if x<246 then 0 else 1)) else (if x<1686 then 0 else (if x<1708 then 1 else 0))) else (if x<1768 then (if x<1740 then 2 else (if x<1746 then 3 else 3)) else (if x<2614 then 2 else (if x<2646 then 1 else 0)))) else (if x<3158 then (if x<2770 then (if x<2674 then 2 else (if x<2764 then 3 else 0)) else (if x<2792 then 1 else (if x<3126 then 4 else 4))) else (if x<3222 then (if x<3180 then 1 else (if x<3186 then 4 else 0)) else (if x<3244 then 2 else (if x<3250 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10269 : Finset ℕ := ([136,246,1708,1746,2646,2674,2770,3158,3186,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10269 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10269 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10269 4 (fun x => (if x<2674 then (if x<1708 then (if x<246 then 0 else 1) else (if x<1746 then 0 else (if x<2646 then 1 else 0))) else (if x<3158 then (if x<2770 then 1 else 2) else (if x<3186 then 1 else (if x<3244 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers10270 : Finset ℕ := ([18,72,136,246,1590,1686,1708,1714,1740,1746,1768,2614,2646,2668,2674,2764,2770,2792,3126,3158,3180,3186,3222,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound10270 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10270 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers10270 72 4
  · have he : independentCachedBranchMembers10270.erase 72=independentCachedBranchMembers10268 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10268
  · have he : independentCachedBranchMembers10270.filter (independentCachedEdge 72)=independentCachedBranchMembers10269 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound10269
def independentCachedBranchMembers10271 : Finset ℕ := ([246,1714,1746,1768,2674,2770,2792,3126,3158,3180,3222,3244] : List ℕ).toFinset
theorem independentCachedBranchBound10271 : ListCliqueBound independentCachedEdge independentCachedBranchMembers10271 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers10271 4 (fun x => (if x<2792 then (if x<1768 then (if x<1714 then 0 else (if x<1746 then 0 else 1)) else (if x<2674 then 1 else (if x<2770 then 0 else 2))) else (if x<3180 then (if x<3126 then 2 else (if x<3158 then 0 else 1)) else (if x<3222 then 1 else (if x<3244 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
