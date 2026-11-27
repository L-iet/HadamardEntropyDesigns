/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch161
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers7968 : Finset ℕ := ([36,136,144,192,222,1594,1596,1642,1644,1650,1652,1678,1686,1734,1752,2606,2614,2662,2680,2714,2716,2762,2764,2770,2772,3118,3126,3174,3192,3226,3228,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7968 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7968 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7968 136 4
  · have he : independentCachedBranchMembers7968.erase 136=independentCachedBranchMembers7966 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7966
  · have he : independentCachedBranchMembers7968.filter (independentCachedEdge 136)=independentCachedBranchMembers7967 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7967
def independentCachedBranchMembers7969 : Finset ℕ := ([36,222,1596,1644,1652,1678,1686,1734,2680,2714,2762,2770,3192,3226,3274,3282] : List ℕ).toFinset
theorem independentCachedBranchBound7969 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7969 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7969 4 (fun x => (if x<2680 then (if x<1652 then (if x<1596 then (if x<222 then 0 else 1) else (if x<1644 then 0 else 2)) else (if x<1686 then (if x<1678 then 3 else 1) else (if x<1734 then 3 else 2))) else (if x<3192 then (if x<2762 then (if x<2714 then 2 else 1) else (if x<2770 then 0 else 2)) else (if x<3274 then (if x<3226 then 3 else 3) else (if x<3282 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7970 : Finset ℕ := ([34,36,136,144,192,222,1594,1596,1642,1644,1650,1652,1678,1686,1734,1752,2606,2614,2662,2680,2714,2716,2762,2764,2770,2772,3118,3126,3174,3192,3226,3228,3274,3276,3282,3284] : List ℕ).toFinset
theorem independentCachedBranchBound7970 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7970 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7970 34 4
  · have he : independentCachedBranchMembers7970.erase 34=independentCachedBranchMembers7968 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7968
  · have he : independentCachedBranchMembers7970.filter (independentCachedEdge 34)=independentCachedBranchMembers7969 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7969
def independentCachedBranchMembers7971 : Finset ℕ := ([12,18,34,36,66,68,136,144,160,190,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2560,2590,2606,2614,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7971 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7971 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7971 160 5
  · have he : independentCachedBranchMembers7971.erase 160=independentCachedBranchMembers7947 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7947
  · have he : independentCachedBranchMembers7971.filter (independentCachedEdge 160)=independentCachedBranchMembers7970 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7970
def independentCachedBranchMembers7972 : Finset ℕ := ([68,238,1594,1626,1644,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7972 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7972 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7972 5 (fun x => (if x<2662 then (if x<1702 then (if x<1626 then (if x<238 then 0 else (if x<1594 then 0 else 1)) else (if x<1644 then 2 else (if x<1678 then 0 else 1))) else (if x<1752 then (if x<1720 then 3 else (if x<1734 then 2 else 0)) else (if x<2606 then (if x<1776 then 1 else 3) else (if x<2638 then 1 else 0)))) else (if x<3150 then (if x<2764 then (if x<2680 then 4 else (if x<2714 then 1 else 1)) else (if x<2788 then (if x<2770 then 1 else 4) else (if x<3118 then 0 else 3))) else (if x<3226 then (if x<3174 then 2 else (if x<3192 then 0 else 2)) else (if x<3250 then (if x<3244 then 2 else 2) else (if x<3300 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7973 : Finset ℕ := ([238,1594,1626,1678,1702,1734,2680,2764,2788,3192,3244,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7973 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7973 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7973 4 (fun x => (if x<2680 then (if x<1678 then (if x<1594 then 0 else (if x<1626 then 1 else 2)) else (if x<1702 then 0 else (if x<1734 then 1 else 2))) else (if x<3192 then (if x<2764 then 1 else (if x<2788 then 0 else 1)) else (if x<3244 then 2 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7974 : Finset ℕ := ([68,144,238,1594,1626,1644,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7974 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7974 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7974 144 4
  · have he : independentCachedBranchMembers7974.erase 144=independentCachedBranchMembers7972 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7972
  · have he : independentCachedBranchMembers7974.filter (independentCachedEdge 144)=independentCachedBranchMembers7973 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7973
def independentCachedBranchMembers7975 : Finset ℕ := ([68,1594,1678,1720,1734,1776,2638,2680,2764,3150,3192,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7975 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7975 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7975 4 (fun x => (if x<2638 then (if x<1720 then (if x<1594 then 0 else (if x<1678 then 0 else 1)) else (if x<1734 then 1 else (if x<1776 then 2 else 2))) else (if x<3150 then (if x<2680 then 1 else (if x<2764 then 1 else 0)) else (if x<3192 then 2 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7976 : Finset ℕ := ([36,68,144,238,1594,1626,1644,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7976 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7976 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7976 36 4
  · have he : independentCachedBranchMembers7976.erase 36=independentCachedBranchMembers7974 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7974
  · have he : independentCachedBranchMembers7976.filter (independentCachedEdge 36)=independentCachedBranchMembers7975 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7975
def independentCachedBranchMembers7977 : Finset ℕ := ([238,1594,1678,1702,1720,2638,2662,2680,2764,2770,2788,3118,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7977 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7977 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7977 4 (fun x => (if x<2680 then (if x<1702 then (if x<1594 then 0 else (if x<1678 then 1 else 0)) else (if x<2638 then (if x<1720 then 1 else 2) else (if x<2662 then 0 else 2))) else (if x<3118 then (if x<2770 then (if x<2764 then 1 else 3) else (if x<2788 then 3 else 1)) else (if x<3244 then (if x<3226 then 0 else 2) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7978 : Finset ℕ := ([1678,1702,2680,2770,3118,3244] : List ℕ).toFinset
theorem independentCachedBranchBound7978 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7978 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7978 3 (fun x => (if x<2770 then (if x<1702 then 0 else (if x<2680 then 1 else 0)) else (if x<3118 then 2 else (if x<3244 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7979 : Finset ℕ := ([68,238,1594,1678,1702,1720,2638,2662,2680,2764,2770,2788,3118,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7979 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7979 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7979 68 3
  · have he : independentCachedBranchMembers7979.erase 68=independentCachedBranchMembers7977 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7977
  · have he : independentCachedBranchMembers7979.filter (independentCachedEdge 68)=independentCachedBranchMembers7978 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7978
def independentCachedBranchMembers7980 : Finset ℕ := ([36,68,144,238,1594,1626,1644,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7980 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7980 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7980 3282 4
  · have he : independentCachedBranchMembers7980.erase 3282=independentCachedBranchMembers7976 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7976
  · have he : independentCachedBranchMembers7980.filter (independentCachedEdge 3282)=independentCachedBranchMembers7979 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7979
def independentCachedBranchMembers7981 : Finset ℕ := ([144,1626,1702,1720,1776,2606,2662,2680,2714,2764,2770,3150,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7981 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7981 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7981 4 (fun x => (if x<2680 then (if x<1720 then (if x<1626 then 0 else (if x<1702 then 1 else 2)) else (if x<2606 then (if x<1776 then 0 else 1) else (if x<2662 then 2 else 0))) else (if x<3150 then (if x<2764 then (if x<2714 then 1 else 3) else (if x<2770 then 3 else 1)) else (if x<3250 then (if x<3244 then 0 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7982 : Finset ℕ := ([1720,1776,2680,2764,3150,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7982 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7982 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7982 3 (fun x => (if x<2764 then (if x<1776 then 0 else (if x<2680 then 1 else 0)) else (if x<3150 then 2 else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7983 : Finset ℕ := ([36,144,1626,1702,1720,1776,2606,2662,2680,2714,2764,2770,3150,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7983 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7983 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7983 36 3
  · have he : independentCachedBranchMembers7983.erase 36=independentCachedBranchMembers7981 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7981
  · have he : independentCachedBranchMembers7983.filter (independentCachedEdge 36)=independentCachedBranchMembers7982 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7982
def independentCachedBranchMembers7984 : Finset ℕ := ([36,68,144,238,1594,1626,1644,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7984 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7984 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7984 3276 4
  · have he : independentCachedBranchMembers7984.erase 3276=independentCachedBranchMembers7980 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7980
  · have he : independentCachedBranchMembers7984.filter (independentCachedEdge 3276)=independentCachedBranchMembers7983 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7983
def independentCachedBranchMembers7985 : Finset ℕ := ([36,238,1626,1678,1734,1752,2638,2714,2764,2770,3118,3174,3192,3244,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7985 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7985 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7985 4 (fun x => (if x<2764 then (if x<1734 then (if x<1626 then (if x<238 then 0 else 0) else (if x<1678 then 1 else 1)) else (if x<2638 then (if x<1752 then 2 else 2) else (if x<2714 then 1 else 1))) else (if x<3192 then (if x<3118 then (if x<2770 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3250 then (if x<3244 then 3 else 3) else (if x<3300 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7986 : Finset ℕ := ([36,68,144,238,1594,1626,1644,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2738,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7986 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7986 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7986 2738 4
  · have he : independentCachedBranchMembers7986.erase 2738=independentCachedBranchMembers7984 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7984
  · have he : independentCachedBranchMembers7986.filter (independentCachedEdge 2738)=independentCachedBranchMembers7985 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7985
def independentCachedBranchMembers7987 : Finset ℕ := ([68,144,1594,1734,1752,1776,2606,2764,2770,2788,3150,3174,3192,3226,3244,3250] : List ℕ).toFinset
theorem independentCachedBranchBound7987 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7987 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7987 4 (fun x => (if x<2770 then (if x<1752 then (if x<1594 then (if x<144 then 0 else 0) else (if x<1734 then 1 else 2)) else (if x<2606 then (if x<1776 then 1 else 2) else (if x<2764 then 1 else 1))) else (if x<3192 then (if x<3150 then (if x<2788 then 2 else 2) else (if x<3174 then 0 else 3)) else (if x<3244 then (if x<3226 then 3 else 0) else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7988 : Finset ℕ := ([36,68,144,238,1594,1626,1644,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2732,2738,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7988 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7988 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7988 2732 4
  · have he : independentCachedBranchMembers7988.erase 2732=independentCachedBranchMembers7986 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7986
  · have he : independentCachedBranchMembers7988.filter (independentCachedEdge 2732)=independentCachedBranchMembers7987 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7987
def independentCachedBranchMembers7989 : Finset ℕ := ([36,68,144,238,1594,1626,1678,1776,2606,2638,2714,2788,3118,3150,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7989 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7989 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7989 4 (fun x => (if x<2606 then (if x<1594 then (if x<144 then (if x<68 then 0 else 1) else (if x<238 then 0 else 1)) else (if x<1678 then (if x<1626 then 2 else 3) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2714 then (if x<2638 then 0 else 1) else (if x<2788 then 0 else 1)) else (if x<3226 then (if x<3150 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7990 : Finset ℕ := ([36,68,144,238,1594,1626,1644,1650,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2732,2738,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7990 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7990 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7990 1650 4
  · have he : independentCachedBranchMembers7990.erase 1650=independentCachedBranchMembers7988 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7988
  · have he : independentCachedBranchMembers7990.filter (independentCachedEdge 1650)=independentCachedBranchMembers7989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7989
def independentCachedBranchMembers7991 : Finset ℕ := ([238,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,3118,3150,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7991 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7991 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7991 4 (fun x => (if x<2606 then (if x<1720 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<1752 then (if x<1734 then 1 else 2) else (if x<1776 then 2 else 3))) else (if x<3118 then (if x<2662 then (if x<2638 then 0 else 3) else (if x<2680 then 1 else 1)) else (if x<3174 then (if x<3150 then 3 else 0) else (if x<3192 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7992 : Finset ℕ := ([238,1678,1702,1734,2680,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7992 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7992 3 (fun x => (if x<1734 then (if x<1678 then 0 else (if x<1702 then 0 else 1)) else (if x<2680 then 2 else (if x<3192 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7993 : Finset ℕ := ([144,238,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,3118,3150,3174,3192] : List ℕ).toFinset
theorem independentCachedBranchBound7993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7993 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7993 144 3
  · have he : independentCachedBranchMembers7993.erase 144=independentCachedBranchMembers7991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7991
  · have he : independentCachedBranchMembers7993.filter (independentCachedEdge 144)=independentCachedBranchMembers7992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7992
def independentCachedBranchMembers7994 : Finset ℕ := ([18,36,68,144,238,1594,1626,1644,1650,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2732,2738,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7994 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7994 18 4
  · have he : independentCachedBranchMembers7994.erase 18=independentCachedBranchMembers7990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7990
  · have he : independentCachedBranchMembers7994.filter (independentCachedEdge 18)=independentCachedBranchMembers7993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7993
def independentCachedBranchMembers7995 : Finset ℕ := ([36,68,1594,1626,1702,1720,1734,1752,2662,2680,2714,2788,3174,3192,3226,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7995 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7995 4 (fun x => (if x<2662 then (if x<1702 then (if x<1594 then (if x<68 then 0 else 1) else (if x<1626 then 1 else 0)) else (if x<1734 then (if x<1720 then 2 else 2) else (if x<1752 then 3 else 3))) else (if x<3174 then (if x<2714 then (if x<2680 then 2 else 2) else (if x<2788 then 0 else 1)) else (if x<3226 then (if x<3192 then 3 else 3) else (if x<3300 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7996 : Finset ℕ := ([12,18,36,68,144,238,1594,1626,1644,1650,1678,1702,1720,1734,1752,1776,2606,2638,2662,2680,2714,2732,2738,2764,2770,2788,3118,3150,3174,3192,3226,3244,3250,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7996 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7996 12 4
  · have he : independentCachedBranchMembers7996.erase 12=independentCachedBranchMembers7994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7994
  · have he : independentCachedBranchMembers7996.filter (independentCachedEdge 12)=independentCachedBranchMembers7995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7995
def independentCachedBranchMembers7997 : Finset ℕ := ([12,18,20,34,36,66,68,136,144,160,190,192,222,238,246,1594,1596,1626,1628,1642,1644,1650,1652,1678,1686,1702,1720,1734,1752,1768,1776,2560,2590,2606,2614,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2762,2764,2770,2772,2786,2788,3072,3102,3118,3126,3150,3158,3174,3192,3226,3228,3242,3244,3250,3252,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound7997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7997 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers7997 20 5
  · have he : independentCachedBranchMembers7997.erase 20=independentCachedBranchMembers7971 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7971
  · have he : independentCachedBranchMembers7997.filter (independentCachedEdge 20)=independentCachedBranchMembers7996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound7996
def independentCachedBranchMembers7998 : Finset ℕ := ([66,246,1596,1628,1650,1686,1702,1720,1734,1752,1768,2614,2646,2662,2680,2716,2764,2770,2786,3126,3158,3174,3192,3228,3244,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7998 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7998 5 (fun x => (if x<2662 then (if x<1702 then (if x<1628 then (if x<246 then 0 else (if x<1596 then 0 else 1)) else (if x<1650 then 2 else (if x<1686 then 0 else 1))) else (if x<1752 then (if x<1720 then 3 else (if x<1734 then 2 else 0)) else (if x<2614 then (if x<1768 then 1 else 3) else (if x<2646 then 1 else 0)))) else (if x<3158 then (if x<2764 then (if x<2680 then 4 else (if x<2716 then 1 else 1)) else (if x<2786 then (if x<2770 then 4 else 1) else (if x<3126 then 0 else 3))) else (if x<3228 then (if x<3174 then 2 else (if x<3192 then 0 else 2)) else (if x<3250 then (if x<3244 then 2 else 3) else (if x<3298 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers7999 : Finset ℕ := ([246,1596,1628,1686,1702,1734,2680,2770,2786,3192,3250,3298] : List ℕ).toFinset
theorem independentCachedBranchBound7999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers7999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers7999 4 (fun x => (if x<2680 then (if x<1686 then (if x<1596 then 0 else (if x<1628 then 1 else 2)) else (if x<1702 then 0 else (if x<1734 then 1 else 2))) else (if x<3192 then (if x<2770 then 1 else (if x<2786 then 0 else 1)) else (if x<3250 then 2 else (if x<3298 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
