/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch193
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers8992 : Finset ℕ := ([2732,2738,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8992 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8992 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8992 2776 4
  · have he : independentCachedBranchMembers8992.erase 2776=independentCachedBranchMembers8990 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8990
  · have he : independentCachedBranchMembers8992.filter (independentCachedEdge 2776)=independentCachedBranchMembers8991 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8991
def independentCachedBranchMembers8993 : Finset ℕ := ([2762,2772,3118,3126,3162,3164,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8993 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8993 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8993 4 (fun x => (if x<3164 then (if x<3118 then (if x<2772 then 0 else 0) else (if x<3126 then 1 else (if x<3162 then 2 else 1))) else (if x<3228 then (if x<3226 then 2 else 2) else (if x<3304 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8994 : Finset ℕ := ([2732,2738,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8994 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8994 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8994 2758 4
  · have he : independentCachedBranchMembers8994.erase 2758=independentCachedBranchMembers8992 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8992
  · have he : independentCachedBranchMembers8994.filter (independentCachedEdge 2758)=independentCachedBranchMembers8993 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8993
def independentCachedBranchMembers8995 : Finset ℕ := ([2732,2738,3118,3132,3150,3164,3222,3226,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound8995 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8995 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8995 4 (fun x => (if x<3164 then (if x<3118 then (if x<2738 then 0 else 0) else (if x<3132 then 1 else (if x<3150 then 2 else 2))) else (if x<3226 then (if x<3222 then 1 else 1) else (if x<3300 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8996 : Finset ℕ := ([2674,2732,2738,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8996 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8996 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8996 2674 4
  · have he : independentCachedBranchMembers8996.erase 2674=independentCachedBranchMembers8994 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8994
  · have he : independentCachedBranchMembers8996.filter (independentCachedEdge 2674)=independentCachedBranchMembers8995 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8995
def independentCachedBranchMembers8997 : Finset ℕ := ([2732,2738,3126,3130,3158,3162,3214,3228,3298,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8997 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8997 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8997 4 (fun x => (if x<3162 then (if x<3126 then (if x<2738 then 0 else 0) else (if x<3130 then 1 else (if x<3158 then 2 else 2))) else (if x<3228 then (if x<3214 then 1 else 1) else (if x<3298 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers8998 : Finset ℕ := ([2668,2674,2732,2738,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound8998 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8998 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers8998 2668 4
  · have he : independentCachedBranchMembers8998.erase 2668=independentCachedBranchMembers8996 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8996
  · have he : independentCachedBranchMembers8998.filter (independentCachedEdge 2668)=independentCachedBranchMembers8997 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8997
def independentCachedBranchMembers8999 : Finset ℕ := ([2732,2738,2758,2776,3118,3126,3162,3164,3214,3222,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound8999 : ListCliqueBound independentCachedEdge independentCachedBranchMembers8999 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers8999 4 (fun x => (if x<3162 then (if x<2776 then (if x<2738 then 0 else (if x<2758 then 0 else 0)) else (if x<3118 then 0 else (if x<3126 then 1 else 2))) else (if x<3222 then (if x<3164 then 1 else (if x<3214 then 2 else 2)) else (if x<3298 then 1 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9000 : Finset ℕ := ([2668,2674,2732,2738,2744,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9000 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9000 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9000 2744 4
  · have he : independentCachedBranchMembers9000.erase 2744=independentCachedBranchMembers8998 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8998
  · have he : independentCachedBranchMembers9000.filter (independentCachedEdge 2744)=independentCachedBranchMembers8999 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8999
def independentCachedBranchMembers9001 : Finset ℕ := ([2732,2738,2758,2776,3130,3132,3150,3158,3226,3228,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9001 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9001 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9001 4 (fun x => (if x<3150 then (if x<2776 then (if x<2738 then 0 else (if x<2758 then 0 else 0)) else (if x<3130 then 0 else (if x<3132 then 1 else 2))) else (if x<3228 then (if x<3158 then 1 else (if x<3226 then 2 else 2)) else (if x<3304 then 1 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9002 : Finset ℕ := ([2668,2674,2726,2732,2738,2744,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9002 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9002 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9002 2726 4
  · have he : independentCachedBranchMembers9002.erase 2726=independentCachedBranchMembers9000 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9000
  · have he : independentCachedBranchMembers9002.filter (independentCachedEdge 2726)=independentCachedBranchMembers9001 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9001
def independentCachedBranchMembers9003 : Finset ℕ := ([2668,2674,2762,2772,3118,3130,3150,3162,3222,3228,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9003 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9003 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9003 4 (fun x => (if x<3150 then (if x<2772 then (if x<2674 then 0 else (if x<2762 then 0 else 0)) else (if x<3118 then 0 else (if x<3130 then 1 else 2))) else (if x<3228 then (if x<3162 then 2 else (if x<3222 then 1 else 1)) else (if x<3298 then 2 else (if x<3304 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9004 : Finset ℕ := ([2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9004 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9004 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9004 2676 4
  · have he : independentCachedBranchMembers9004.erase 2676=independentCachedBranchMembers9002 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9002
  · have he : independentCachedBranchMembers9004.filter (independentCachedEdge 2676)=independentCachedBranchMembers9003 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9003
def independentCachedBranchMembers9005 : Finset ℕ := ([2668,2674,2762,2772,3126,3132,3158,3164,3214,3226,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9005 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9005 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9005 4 (fun x => (if x<3158 then (if x<2772 then (if x<2674 then 0 else (if x<2762 then 0 else 0)) else (if x<3126 then 0 else (if x<3132 then 1 else 2))) else (if x<3226 then (if x<3164 then 2 else (if x<3214 then 1 else 1)) else (if x<3300 then 2 else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9006 : Finset ℕ := ([2666,2668,2674,2676,2726,2732,2738,2744,2758,2762,2772,2776,3118,3126,3130,3132,3150,3158,3162,3164,3214,3222,3226,3228,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9006 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9006 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9006 2666 4
  · have he : independentCachedBranchMembers9006.erase 2666=independentCachedBranchMembers9004 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9004
  · have he : independentCachedBranchMembers9006.filter (independentCachedEdge 2666)=independentCachedBranchMembers9005 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9005
def independentCachedBranchMembers9007 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2732,2738,2744,2758,2762,2772,2776,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9007 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9007 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9007 3102 5
  · have he : independentCachedBranchMembers9007.erase 3102=independentCachedBranchMembers8989 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound8989
  · have he : independentCachedBranchMembers9007.filter (independentCachedEdge 3102)=independentCachedBranchMembers9006 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9006
def independentCachedBranchMembers9008 : Finset ℕ := ([2668,2710,2732,2744,2762,2776,2800,3072,3118,3132,3150,3162,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9008 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9008 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9008 5 (fun x => (if x<3174 then (if x<2800 then (if x<2744 then (if x<2710 then 0 else (if x<2732 then 1 else 1)) else (if x<2762 then 0 else (if x<2776 then 0 else 1))) else (if x<3132 then (if x<3072 then 2 else (if x<3118 then 3 else 2)) else (if x<3150 then 0 else (if x<3162 then 0 else 3)))) else (if x<3238 then (if x<3214 then (if x<3186 then 3 else (if x<3188 then 2 else 4)) else (if x<3226 then 3 else (if x<3228 then 0 else 1))) else (if x<3270 then (if x<3250 then 1 else (if x<3252 then 3 else 2)) else (if x<3284 then (if x<3282 then 4 else 1) else (if x<3304 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9009 : Finset ℕ := ([2668,2710,2762,3072,3132,3188,3214,3226,3238,3250,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound9009 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9009 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9009 4 (fun x => (if x<3214 then (if x<3072 then (if x<2710 then 0 else (if x<2762 then 1 else 0)) else (if x<3132 then 2 else (if x<3188 then 0 else 2))) else (if x<3250 then (if x<3226 then 1 else (if x<3238 then 0 else 2)) else (if x<3270 then 1 else (if x<3282 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9010 : Finset ℕ := ([2666,2668,2710,2732,2744,2762,2776,2800,3072,3118,3132,3150,3162,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9010 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9010 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9010 2666 4
  · have he : independentCachedBranchMembers9010.erase 2666=independentCachedBranchMembers9008 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9008
  · have he : independentCachedBranchMembers9010.filter (independentCachedEdge 2666)=independentCachedBranchMembers9009 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9009
def independentCachedBranchMembers9011 : Finset ℕ := ([2666,2710,2732,2744,2762,2800,3132,3150,3162,3188,3228,3238,3250,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9011 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9011 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9011 4 (fun x => (if x<3150 then (if x<2744 then (if x<2710 then 0 else (if x<2732 then 1 else 0)) else (if x<2800 then (if x<2762 then 1 else 1) else (if x<3132 then 0 else 2))) else (if x<3228 then (if x<3162 then 2 else (if x<3188 then 3 else 3)) else (if x<3250 then (if x<3238 then 3 else 2) else (if x<3284 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9012 : Finset ℕ := ([2666,2668,2710,2732,2744,2762,2776,2800,3072,3118,3132,3150,3162,3164,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9012 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9012 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9012 3164 4
  · have he : independentCachedBranchMembers9012.erase 3164=independentCachedBranchMembers9010 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9010
  · have he : independentCachedBranchMembers9012.filter (independentCachedEdge 3164)=independentCachedBranchMembers9011 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9011
def independentCachedBranchMembers9013 : Finset ℕ := ([2668,2710,2732,2762,2776,2800,3118,3132,3162,3186,3226,3250,3270,3284] : List ℕ).toFinset
theorem independentCachedBranchBound9013 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9013 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9013 4 (fun x => (if x<3132 then (if x<2762 then (if x<2710 then 0 else (if x<2732 then 1 else 1)) else (if x<2800 then (if x<2776 then 0 else 1) else (if x<3118 then 0 else 2))) else (if x<3226 then (if x<3162 then 3 else (if x<3186 then 2 else 3)) else (if x<3270 then (if x<3250 then 3 else 2) else (if x<3284 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9014 : Finset ℕ := ([2666,2668,2710,2732,2744,2762,2776,2800,3072,3118,3130,3132,3150,3162,3164,3174,3186,3188,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9014 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9014 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9014 3130 4
  · have he : independentCachedBranchMembers9014.erase 3130=independentCachedBranchMembers9012 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9012
  · have he : independentCachedBranchMembers9014.filter (independentCachedEdge 3130)=independentCachedBranchMembers9013 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9013
def independentCachedBranchMembers9015 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2710,2726,2732,2738,2744,2758,2762,2772,2776,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9015 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9015 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9015 2792 5
  · have he : independentCachedBranchMembers9015.erase 2792=independentCachedBranchMembers9007 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9007
  · have he : independentCachedBranchMembers9015.filter (independentCachedEdge 2792)=independentCachedBranchMembers9014 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9014
def independentCachedBranchMembers9016 : Finset ℕ := ([2674,2676,2710,2726,2732,2758,2762,2800,3072,3126,3130,3132,3158,3162,3164,3174,3178,3180,3214,3250,3252,3256,3282,3284,3288,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound9016 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9016 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9016 5 (fun x => (if x<3164 then (if x<2800 then (if x<2726 then (if x<2676 then 0 else (if x<2710 then 1 else 0)) else (if x<2758 then (if x<2732 then 1 else 2) else (if x<2762 then 2 else 0))) else (if x<3130 then (if x<3072 then 2 else (if x<3126 then 3 else 0)) else (if x<3158 then (if x<3132 then 3 else 4) else (if x<3162 then 3 else 4)))) else (if x<3256 then (if x<3180 then (if x<3174 then 1 else (if x<3178 then 1 else 0)) else (if x<3250 then (if x<3214 then 3 else 0) else (if x<3252 then 4 else 1))) else (if x<3288 then (if x<3282 then 2 else (if x<3284 then 0 else 4)) else (if x<3300 then (if x<3298 then 3 else 3) else (if x<3304 then 2 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9017 : Finset ℕ := ([2620,2650,2666,2668,2674,2676,2702,2710,2726,2732,2738,2744,2758,2762,2772,2776,2792,2800,3072,3102,3118,3126,3130,3132,3150,3158,3162,3164,3174,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9017 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9017 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9017 2702 5
  · have he : independentCachedBranchMembers9017.erase 2702=independentCachedBranchMembers9015 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9015
  · have he : independentCachedBranchMembers9017.filter (independentCachedEdge 2702)=independentCachedBranchMembers9016 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9016
def independentCachedBranchMembers9018 : Finset ℕ := ([2620,2650,2676,2738,2772,2776,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9018 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9018 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9018 5 (fun x => (if x<3178 then (if x<3072 then (if x<2738 then (if x<2650 then 0 else (if x<2676 then 0 else 1)) else (if x<2772 then 0 else (if x<2776 then 0 else 1))) else (if x<3130 then (if x<3118 then 2 else (if x<3126 then 2 else 1)) else (if x<3164 then 0 else (if x<3174 then 0 else 3)))) else (if x<3256 then (if x<3226 then (if x<3186 then 4 else (if x<3222 then 2 else 2)) else (if x<3244 then 1 else (if x<3252 then 3 else 0))) else (if x<3282 then (if x<3270 then 2 else (if x<3274 then 4 else 2)) else (if x<3300 then 0 else (if x<3312 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9019 : Finset ℕ := ([2650,2738,2776,3072,3130,3178,3186,3226,3256,3274,3282,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9019 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9019 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9019 4 (fun x => (if x<3186 then (if x<3072 then (if x<2738 then 0 else (if x<2776 then 0 else 1)) else (if x<3130 then 2 else (if x<3178 then 0 else 2))) else (if x<3274 then (if x<3226 then 3 else (if x<3256 then 1 else 2)) else (if x<3282 then 3 else (if x<3312 then 0 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9020 : Finset ℕ := ([2620,2650,2676,2726,2738,2772,2776,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9020 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9020 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9020 2726 4
  · have he : independentCachedBranchMembers9020.erase 2726=independentCachedBranchMembers9018 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9018
  · have he : independentCachedBranchMembers9020.filter (independentCachedEdge 2726)=independentCachedBranchMembers9019 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9019
def independentCachedBranchMembers9021 : Finset ℕ := ([2620,2676,2738,3072,3126,3130,3186,3252,3256,3270,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9021 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9021 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9021 4 (fun x => (if x<3186 then (if x<3072 then (if x<2676 then 0 else (if x<2738 then 1 else 0)) else (if x<3126 then 2 else (if x<3130 then 0 else 2))) else (if x<3270 then (if x<3252 then 1 else (if x<3256 then 1 else 0)) else (if x<3274 then 3 else (if x<3312 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers9022 : Finset ℕ := ([2620,2650,2668,2676,2726,2738,2772,2776,3072,3118,3126,3130,3164,3174,3178,3186,3222,3226,3244,3252,3256,3270,3274,3282,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9022 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9022 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers9022 2668 4
  · have he : independentCachedBranchMembers9022.erase 2668=independentCachedBranchMembers9020 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9020
  · have he : independentCachedBranchMembers9022.filter (independentCachedEdge 2668)=independentCachedBranchMembers9021 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound9021
def independentCachedBranchMembers9023 : Finset ℕ := ([2620,2650,2676,2726,2738,2772,3126,3178,3222,3244,3256,3274,3300,3312] : List ℕ).toFinset
theorem independentCachedBranchBound9023 : ListCliqueBound independentCachedEdge independentCachedBranchMembers9023 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers9023 4 (fun x => (if x<3178 then (if x<2726 then (if x<2650 then 0 else (if x<2676 then 0 else 1)) else (if x<2772 then (if x<2738 then 1 else 0) else (if x<3126 then 0 else 1))) else (if x<3256 then (if x<3222 then 2 else (if x<3244 then 3 else 2)) else (if x<3300 then (if x<3274 then 3 else 3) else (if x<3312 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
