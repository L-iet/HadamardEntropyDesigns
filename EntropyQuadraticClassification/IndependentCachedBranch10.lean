/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch9
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers1280 : Finset ℕ := ([12,252,1596,1650,1720,1740,1764,2618,2638,2652,2710,2732,2762,2776,2800,3180,3214,3228,3252,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1280 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1280 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1280 5 (fun x => (if x<2710 then (if x<1740 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1650 then 0 else (if x<1720 then 1 else 1))) else (if x<2618 then (if x<1764 then 0 else 1) else (if x<2638 then 1 else (if x<2652 then 2 else 0)))) else (if x<3180 then (if x<2762 then (if x<2732 then 2 else 0) else (if x<2776 then 3 else (if x<2800 then 2 else 1))) else (if x<3252 then (if x<3214 then 0 else (if x<3228 then 3 else 0)) else (if x<3282 then 3 else (if x<3304 then 3 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1281 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1281 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1281 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1281 1594 5
  · have he : independentCachedBranchMembers1281.erase 1594=independentCachedBranchMembers1279 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1279
  · have he : independentCachedBranchMembers1281.filter (independentCachedEdge 1594)=independentCachedBranchMembers1280 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1280
def independentCachedBranchMembers1282 : Finset ℕ := ([12,48,252,1596,1628,1650,1708,1740,1776,2620,2638,2652,2674,2732,2764,2800,3102,3180,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1282 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1282 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1282 5 (fun x => (if x<2652 then (if x<1650 then (if x<252 then (if x<48 then 0 else 0) else (if x<1596 then 0 else (if x<1628 then 0 else 1))) else (if x<1776 then (if x<1708 then 1 else (if x<1740 then 2 else 0)) else (if x<2620 then 0 else (if x<2638 then 2 else 3)))) else (if x<3102 then (if x<2732 then (if x<2674 then 4 else 2) else (if x<2764 then 3 else (if x<2800 then 1 else 4))) else (if x<3228 then (if x<3180 then 4 else (if x<3214 then 3 else 3)) else (if x<3250 then 1 else (if x<3282 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1283 : Finset ℕ := ([252,1628,1740,1776,2620,2638,2674,2732,3228,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1283 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1283 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1283 4 (fun x => (if x<2638 then (if x<1740 then (if x<1628 then 0 else 0) else (if x<1776 then 1 else (if x<2620 then 0 else 2))) else (if x<2732 then (if x<2674 then 1 else 1) else (if x<3228 then 3 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1284 : Finset ℕ := ([12,48,252,1596,1614,1628,1650,1708,1740,1776,2620,2638,2652,2674,2732,2764,2800,3102,3180,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1284 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1284 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1284 1614 4
  · have he : independentCachedBranchMembers1284.erase 1614=independentCachedBranchMembers1282 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1282
  · have he : independentCachedBranchMembers1284.filter (independentCachedEdge 1614)=independentCachedBranchMembers1283 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1283
def independentCachedBranchMembers1285 : Finset ℕ := ([1614,1628,1650,1708,2638,2652,2674,2732,3180,3214,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1285 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1285 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1285 4 (fun x => (if x<2674 then (if x<1708 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<2638 then 1 else (if x<2652 then 2 else 3))) else (if x<3214 then (if x<2732 then 2 else (if x<3180 then 3 else 1)) else (if x<3228 then 0 else (if x<3250 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1286 : Finset ℕ := ([12,48,192,252,1596,1614,1628,1650,1708,1740,1776,2620,2638,2652,2674,2732,2764,2800,3102,3180,3214,3228,3250,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1286 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1286 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1286 192 4
  · have he : independentCachedBranchMembers1286.erase 192=independentCachedBranchMembers1284 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1284
  · have he : independentCachedBranchMembers1286.filter (independentCachedEdge 192)=independentCachedBranchMembers1285 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1285
def independentCachedBranchMembers1287 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3180,3192,3214,3226,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1287 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1287 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1287 3226 5
  · have he : independentCachedBranchMembers1287.erase 3226=independentCachedBranchMembers1281 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1281
  · have he : independentCachedBranchMembers1287.filter (independentCachedEdge 3226)=independentCachedBranchMembers1286 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1286
def independentCachedBranchMembers1288 : Finset ℕ := ([48,192,252,1596,1738,1740,1752,1764,1776,2618,2620,2762,2764,2776,2788,2800,3102,3126,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1288 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1288 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1288 5 (fun x => (if x<2762 then (if x<1740 then (if x<252 then (if x<192 then 0 else 0) else (if x<1596 then 0 else (if x<1738 then 0 else 1))) else (if x<1776 then (if x<1752 then 0 else (if x<1764 then 2 else 1)) else (if x<2618 then 0 else (if x<2620 then 3 else 4)))) else (if x<3102 then (if x<2776 then (if x<2764 then 2 else 1) else (if x<2788 then 3 else (if x<2800 then 4 else 2))) else (if x<3282 then (if x<3126 then 4 else (if x<3270 then 3 else 1)) else (if x<3284 then 2 else (if x<3304 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1289 : Finset ℕ := ([252,1596,1740,1764,2618,2762,2776,2800,3282,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1289 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1289 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1289 4 (fun x => (if x<2762 then (if x<1740 then (if x<1596 then 0 else 0) else (if x<1764 then 0 else (if x<2618 then 1 else 1))) else (if x<2800 then (if x<2776 then 2 else 3) else (if x<3282 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1290 : Finset ℕ := ([48,192,252,1594,1596,1738,1740,1752,1764,1776,2618,2620,2762,2764,2776,2788,2800,3102,3126,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1290 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1290 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1290 1594 4
  · have he : independentCachedBranchMembers1290.erase 1594=independentCachedBranchMembers1288 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1288
  · have he : independentCachedBranchMembers1290.filter (independentCachedEdge 1594)=independentCachedBranchMembers1289 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1289
def independentCachedBranchMembers1291 : Finset ℕ := ([1594,1738,1752,1764,2618,2762,2776,2788,3126,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1291 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1291 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1291 4 (fun x => (if x<2776 then (if x<1764 then (if x<1738 then 0 else (if x<1752 then 0 else 1)) else (if x<2618 then 1 else (if x<2762 then 2 else 2))) else (if x<3270 then (if x<2788 then 3 else (if x<3126 then 3 else 0)) else (if x<3284 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1292 : Finset ℕ := ([12,48,192,252,1594,1596,1738,1740,1752,1764,1776,2618,2620,2762,2764,2776,2788,2800,3102,3126,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1292 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1292 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1292 12 4
  · have he : independentCachedBranchMembers1292.erase 12=independentCachedBranchMembers1290 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1290
  · have he : independentCachedBranchMembers1292.filter (independentCachedEdge 12)=independentCachedBranchMembers1291 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1291
def independentCachedBranchMembers1293 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2674,2710,2732,2762,2764,2776,2788,2800,3102,3126,3158,3180,3192,3214,3226,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1293 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1293 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1293 3158 5
  · have he : independentCachedBranchMembers1293.erase 3158=independentCachedBranchMembers1287 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1287
  · have he : independentCachedBranchMembers1293.filter (independentCachedEdge 3158)=independentCachedBranchMembers1292 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1292
def independentCachedBranchMembers1294 : Finset ℕ := ([12,48,192,252,1596,1614,1650,1686,1740,1752,1764,1776,2618,2652,2732,2762,3102,3126,3180,3192,3228,3252,3270,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1294 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1294 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1294 5 (fun x => (if x<2618 then (if x<1650 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1596 then 0 else (if x<1614 then 0 else 1))) else (if x<1752 then (if x<1686 then 1 else (if x<1740 then 1 else 0)) else (if x<1764 then 1 else (if x<1776 then 1 else 0)))) else (if x<3180 then (if x<2762 then (if x<2652 then 2 else (if x<2732 then 2 else 2)) else (if x<3102 then 2 else (if x<3126 then 3 else 4))) else (if x<3252 then (if x<3192 then 3 else (if x<3228 then 4 else 4)) else (if x<3270 then 3 else (if x<3282 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1295 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2674,2710,2730,2732,2762,2764,2776,2788,2800,3102,3126,3158,3180,3192,3214,3226,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1295 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1295 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1295 2730 5
  · have he : independentCachedBranchMembers1295.erase 2730=independentCachedBranchMembers1293 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1293
  · have he : independentCachedBranchMembers1295.filter (independentCachedEdge 2730)=independentCachedBranchMembers1294 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1294
def independentCachedBranchMembers1296 : Finset ℕ := ([12,48,192,252,1594,1596,1628,1686,1708,1738,1740,1776,2638,2674,2776,2788,3102,3192,3214,3250,3252,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1296 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1296 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1296 5 (fun x => (if x<2638 then (if x<1628 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1594 then 0 else (if x<1596 then 1 else 0))) else (if x<1738 then (if x<1686 then 1 else (if x<1708 then 1 else 1)) else (if x<1740 then 1 else (if x<1776 then 0 else 0)))) else (if x<3214 then (if x<2788 then (if x<2674 then 2 else (if x<2776 then 2 else 2)) else (if x<3102 then 2 else (if x<3192 then 3 else 3))) else (if x<3282 then (if x<3250 then 4 else (if x<3252 then 3 else 4)) else (if x<3284 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1297 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2764,2776,2788,2800,3102,3126,3158,3180,3192,3214,3226,3228,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1297 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1297 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1297 2662 5
  · have he : independentCachedBranchMembers1297.erase 2662=independentCachedBranchMembers1295 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1295
  · have he : independentCachedBranchMembers1297.filter (independentCachedEdge 2662)=independentCachedBranchMembers1296 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1296
def independentCachedBranchMembers1298 : Finset ℕ := ([12,48,192,1650,1720,1738,1740,2618,2620,2638,2764,2800,3126,3214,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1298 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1298 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1298 5 (fun x => (if x<2620 then (if x<1720 then (if x<192 then (if x<48 then 0 else 0) else (if x<1650 then 0 else 1)) else (if x<1740 then (if x<1738 then 1 else 1) else (if x<2618 then 0 else 2))) else (if x<3126 then (if x<2764 then (if x<2638 then 3 else 2) else (if x<2800 then 3 else 3)) else (if x<3250 then (if x<3214 then 4 else 4) else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1299 : Finset ℕ := ([12,192,1650,1740,2618,2764,3126,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1299 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1299 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1299 4 (fun x => (if x<2618 then (if x<1650 then (if x<192 then 0 else 0) else (if x<1740 then 1 else 0)) else (if x<3126 then (if x<2764 then 1 else 2) else (if x<3250 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1300 : Finset ℕ := ([12,48,192,1650,1720,1738,1740,2618,2620,2638,2764,2800,3126,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1300 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1300 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1300 3252 4
  · have he : independentCachedBranchMembers1300.erase 3252=independentCachedBranchMembers1298 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1298
  · have he : independentCachedBranchMembers1300.filter (independentCachedEdge 3252)=independentCachedBranchMembers1299 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1299
def independentCachedBranchMembers1301 : Finset ℕ := ([12,192,1738,1740,2638,2764,3214,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1301 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1301 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1301 4 (fun x => (if x<2638 then (if x<1738 then (if x<192 then 0 else 0) else (if x<1740 then 1 else 0)) else (if x<3214 then (if x<2764 then 1 else 2) else (if x<3270 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1302 : Finset ℕ := ([12,48,192,1650,1720,1738,1740,2618,2620,2638,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1302 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1302 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1302 3192 4
  · have he : independentCachedBranchMembers1302.erase 3192=independentCachedBranchMembers1300 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1300
  · have he : independentCachedBranchMembers1302.filter (independentCachedEdge 3192)=independentCachedBranchMembers1301 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1301
def independentCachedBranchMembers1303 : Finset ℕ := ([1650,1720,2618,2620,2764,2800,3126,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1303 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1303 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1303 4 (fun x => (if x<2764 then (if x<2618 then (if x<1720 then 0 else 0) else (if x<2620 then 0 else 1)) else (if x<3126 then (if x<2800 then 1 else 0) else (if x<3270 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1304 : Finset ℕ := ([12,48,192,1650,1720,1738,1740,1776,2618,2620,2638,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1304 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1304 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1304 1776 4
  · have he : independentCachedBranchMembers1304.erase 1776=independentCachedBranchMembers1302 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1302
  · have he : independentCachedBranchMembers1304.filter (independentCachedEdge 1776)=independentCachedBranchMembers1303 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1303
def independentCachedBranchMembers1305 : Finset ℕ := ([1720,1738,2620,2638,2764,2800,3214,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1305 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1305 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1305 4 (fun x => (if x<2764 then (if x<2620 then (if x<1738 then 0 else 0) else (if x<2638 then 0 else 0)) else (if x<3214 then (if x<2800 then 1 else 1) else (if x<3250 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1306 : Finset ℕ := ([12,48,192,1596,1650,1720,1738,1740,1776,2618,2620,2638,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1306 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1306 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1306 1596 4
  · have he : independentCachedBranchMembers1306.erase 1596=independentCachedBranchMembers1304 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1304
  · have he : independentCachedBranchMembers1306.filter (independentCachedEdge 1596)=independentCachedBranchMembers1305 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1305
def independentCachedBranchMembers1307 : Finset ℕ := ([12,1650,1720,1738,1776,2620,2638,2764,3192,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1307 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1307 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1307 4 (fun x => (if x<2620 then (if x<1720 then (if x<1650 then 0 else 0) else (if x<1738 then 1 else (if x<1776 then 1 else 2))) else (if x<2764 then (if x<2638 then 1 else 1) else (if x<3192 then 0 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1308 : Finset ℕ := ([12,48,192,1596,1650,1720,1738,1740,1776,2618,2620,2638,2762,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1308 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1308 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1308 2762 4
  · have he : independentCachedBranchMembers1308.erase 2762=independentCachedBranchMembers1306 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1306
  · have he : independentCachedBranchMembers1308.filter (independentCachedEdge 2762)=independentCachedBranchMembers1307 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1307
def independentCachedBranchMembers1309 : Finset ℕ := ([192,1596,1650,1720,1738,2618,2764,2800,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1309 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1309 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1309 4 (fun x => (if x<2618 then (if x<1650 then (if x<1596 then 0 else 0) else (if x<1720 then 1 else (if x<1738 then 1 else 1))) else (if x<2800 then (if x<2764 then 0 else 2) else (if x<3252 then 2 else (if x<3270 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1310 : Finset ℕ := ([12,48,192,1596,1650,1720,1738,1740,1776,2618,2620,2638,2674,2762,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1310 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1310 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1310 2674 4
  · have he : independentCachedBranchMembers1310.erase 2674=independentCachedBranchMembers1308 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1308
  · have he : independentCachedBranchMembers1310.filter (independentCachedEdge 2674)=independentCachedBranchMembers1309 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1309
def independentCachedBranchMembers1311 : Finset ℕ := ([12,192,1596,1650,1738,1776,2618,2638,2764,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1311 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1311 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1311 4 (fun x => (if x<1776 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1650 then 0 else (if x<1738 then 1 else 1))) else (if x<2764 then (if x<2618 then 0 else (if x<2638 then 2 else 2)) else (if x<3250 then 1 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1312 : Finset ℕ := ([12,48,192,1596,1650,1652,1720,1738,1740,1776,2618,2620,2638,2674,2762,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1312 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1312 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1312 1652 4
  · have he : independentCachedBranchMembers1312.erase 1652=independentCachedBranchMembers1310 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1310
  · have he : independentCachedBranchMembers1312.filter (independentCachedEdge 1652)=independentCachedBranchMembers1311 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1311
def independentCachedBranchMembers1313 : Finset ℕ := ([192,1720,1738,1740,1776,2618,2620,2638,2674,3126,3192] : List ℕ).toFinset
theorem independentCachedBranchBound1313 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1313 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1313 4 (fun x => (if x<2618 then (if x<1738 then (if x<1720 then 0 else 1) else (if x<1740 then 0 else (if x<1776 then 1 else 0))) else (if x<2674 then (if x<2620 then 1 else (if x<2638 then 2 else 1)) else (if x<3126 then 2 else (if x<3192 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1314 : Finset ℕ := ([12,48,192,1596,1614,1650,1652,1720,1738,1740,1776,2618,2620,2638,2674,2762,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1314 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1314 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1314 1614 4
  · have he : independentCachedBranchMembers1314.erase 1614=independentCachedBranchMembers1312 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1312
  · have he : independentCachedBranchMembers1314.filter (independentCachedEdge 1614)=independentCachedBranchMembers1313 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1313
def independentCachedBranchMembers1315 : Finset ℕ := ([12,1596,1650,1720,1740,2618,2638,2762,2800,3214,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1315 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1315 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1315 4 (fun x => (if x<2618 then (if x<1650 then (if x<1596 then 0 else 0) else (if x<1720 then 0 else (if x<1740 then 1 else 1))) else (if x<2800 then (if x<2638 then 1 else (if x<2762 then 1 else 2)) else (if x<3214 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1316 : Finset ℕ := ([12,48,192,1594,1596,1614,1650,1652,1720,1738,1740,1776,2618,2620,2638,2674,2762,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1316 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1316 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1316 1594 4
  · have he : independentCachedBranchMembers1316.erase 1594=independentCachedBranchMembers1314 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1314
  · have he : independentCachedBranchMembers1316.filter (independentCachedEdge 1594)=independentCachedBranchMembers1315 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1315
def independentCachedBranchMembers1317 : Finset ℕ := ([1594,1614,1650,1738,2618,2638,2674,2762,3126,3214,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1317 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1317 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1317 4 (fun x => (if x<2674 then (if x<1738 then (if x<1614 then 0 else (if x<1650 then 0 else 1)) else (if x<2618 then 1 else (if x<2638 then 2 else 2))) else (if x<3214 then (if x<2762 then 3 else (if x<3126 then 3 else 1)) else (if x<3250 then 1 else (if x<3270 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1318 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1650,1652,1720,1738,1740,1776,2618,2620,2638,2674,2762,2764,2800,3126,3192,3214,3250,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1318 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1318 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1318 252 4
  · have he : independentCachedBranchMembers1318.erase 252=independentCachedBranchMembers1316 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1316
  · have he : independentCachedBranchMembers1318.filter (independentCachedEdge 252)=independentCachedBranchMembers1317 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1317
def independentCachedBranchMembers1319 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2764,2776,2788,2800,3102,3126,3158,3180,3192,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1319 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1319 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1319 3238 5
  · have he : independentCachedBranchMembers1319.erase 3238=independentCachedBranchMembers1297 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1297
  · have he : independentCachedBranchMembers1319.filter (independentCachedEdge 3238)=independentCachedBranchMembers1318 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1318
def independentCachedBranchMembers1320 : Finset ℕ := ([12,192,252,1628,1652,1708,1720,1740,1776,2620,2652,2732,2764,2776,2788,2800,3180,3192,3228,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1320 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1320 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1320 5 (fun x => (if x<2732 then (if x<1708 then (if x<252 then (if x<192 then 0 else 0) else (if x<1628 then 0 else (if x<1652 then 1 else 2))) else (if x<1776 then (if x<1720 then 1 else (if x<1740 then 2 else 0)) else (if x<2620 then 0 else (if x<2652 then 1 else 3)))) else (if x<3180 then (if x<2776 then (if x<2764 then 3 else 1) else (if x<2788 then 4 else (if x<2800 then 4 else 2))) else (if x<3252 then (if x<3192 then 1 else (if x<3228 then 2 else 1)) else (if x<3284 then 2 else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1321 : Finset ℕ := ([12,1652,1708,1740,1776,2620,2652,2776,2788,3192,3228] : List ℕ).toFinset
theorem independentCachedBranchBound1321 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1321 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1321 4 (fun x => (if x<2620 then (if x<1708 then (if x<1652 then 0 else 1) else (if x<1740 then 0 else (if x<1776 then 1 else 0))) else (if x<2788 then (if x<2652 then 2 else (if x<2776 then 1 else 2)) else (if x<3192 then 1 else (if x<3228 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1322 : Finset ℕ := ([12,192,252,1628,1652,1708,1720,1740,1764,1776,2620,2652,2732,2764,2776,2788,2800,3180,3192,3228,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1322 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1322 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1322 1764 4
  · have he : independentCachedBranchMembers1322.erase 1764=independentCachedBranchMembers1320 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1320
  · have he : independentCachedBranchMembers1322.filter (independentCachedEdge 1764)=independentCachedBranchMembers1321 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1321
def independentCachedBranchMembers1323 : Finset ℕ := ([12,1628,1720,1740,1776,2620,2732,2776,2788,3180,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1323 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1323 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1323 4 (fun x => (if x<2620 then (if x<1720 then (if x<1628 then 0 else 0) else (if x<1740 then 1 else (if x<1776 then 1 else 0))) else (if x<2788 then (if x<2732 then 2 else (if x<2776 then 1 else 1)) else (if x<3180 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1324 : Finset ℕ := ([12,192,252,1628,1652,1708,1720,1740,1752,1764,1776,2620,2652,2732,2764,2776,2788,2800,3180,3192,3228,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1324 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1324 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1324 1752 4
  · have he : independentCachedBranchMembers1324.erase 1752=independentCachedBranchMembers1322 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1322
  · have he : independentCachedBranchMembers1324.filter (independentCachedEdge 1752)=independentCachedBranchMembers1323 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1323
def independentCachedBranchMembers1325 : Finset ℕ := ([1628,1652,1708,1720,2620,2764,2776,2788,2800,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1325 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1325 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1325 4 (fun x => (if x<2764 then (if x<1708 then (if x<1652 then 0 else 1) else (if x<1720 then 0 else (if x<2620 then 1 else 0))) else (if x<2800 then (if x<2776 then 0 else (if x<2788 then 2 else 2)) else (if x<3284 then 1 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1326 : Finset ℕ := ([12,192,252,1596,1628,1652,1708,1720,1740,1752,1764,1776,2620,2652,2732,2764,2776,2788,2800,3180,3192,3228,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1326 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1326 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1326 1596 4
  · have he : independentCachedBranchMembers1326.erase 1596=independentCachedBranchMembers1324 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1324
  · have he : independentCachedBranchMembers1326.filter (independentCachedEdge 1596)=independentCachedBranchMembers1325 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1325
def independentCachedBranchMembers1327 : Finset ℕ := ([1628,1708,1752,1764,2652,2732,2776,2788,3180,3228,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1327 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1327 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1327 4 (fun x => (if x<2776 then (if x<1764 then (if x<1708 then 0 else (if x<1752 then 0 else 1)) else (if x<2652 then 1 else (if x<2732 then 2 else 2))) else (if x<3228 then (if x<2788 then 3 else (if x<3180 then 3 else 0)) else (if x<3284 then 0 else (if x<3304 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1328 : Finset ℕ := ([12,48,192,252,1596,1628,1652,1708,1720,1740,1752,1764,1776,2620,2652,2732,2764,2776,2788,2800,3180,3192,3228,3252,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1328 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1328 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1328 48 4
  · have he : independentCachedBranchMembers1328.erase 48=independentCachedBranchMembers1326 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1326
  · have he : independentCachedBranchMembers1328.filter (independentCachedEdge 48)=independentCachedBranchMembers1327 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1327
def independentCachedBranchMembers1329 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2764,2776,2788,2800,3102,3126,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1329 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1329 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1329 3178 5
  · have he : independentCachedBranchMembers1329.erase 3178=independentCachedBranchMembers1319 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1319
  · have he : independentCachedBranchMembers1329.filter (independentCachedEdge 3178)=independentCachedBranchMembers1328 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1328
def independentCachedBranchMembers1330 : Finset ℕ := ([1594,1614,1652,1686,1708,1752,2620,2652,2662,2674,2730,2762,2788,2800,3126,3158,3180,3192,3214,3226,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1330 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1330 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1330 5 (fun x => (if x<2762 then (if x<1752 then (if x<1652 then (if x<1614 then 0 else 0) else (if x<1686 then 0 else (if x<1708 then 0 else 0))) else (if x<2662 then (if x<2620 then 0 else (if x<2652 then 1 else 2)) else (if x<2674 then 1 else (if x<2730 then 2 else 1)))) else (if x<3180 then (if x<2800 then (if x<2788 then 2 else 2) else (if x<3126 then 1 else (if x<3158 then 3 else 4))) else (if x<3226 then (if x<3192 then 3 else (if x<3214 then 4 else 3)) else (if x<3252 then 4 else (if x<3284 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1331 : Finset ℕ := ([1594,1614,1686,2662,2674,2730,2762,3126,3158,3214,3226] : List ℕ).toFinset
theorem independentCachedBranchBound1331 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1331 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1331 4 (fun x => (if x<2730 then (if x<1686 then (if x<1614 then 0 else 0) else (if x<2662 then 0 else (if x<2674 then 1 else 2))) else (if x<3158 then (if x<2762 then 1 else (if x<3126 then 2 else 2)) else (if x<3214 then 1 else (if x<3226 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1332 : Finset ℕ := ([252,1594,1614,1652,1686,1708,1752,2620,2652,2662,2674,2730,2762,2788,2800,3126,3158,3180,3192,3214,3226,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1332 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1332 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1332 252 4
  · have he : independentCachedBranchMembers1332.erase 252=independentCachedBranchMembers1330 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1330
  · have he : independentCachedBranchMembers1332.filter (independentCachedEdge 252)=independentCachedBranchMembers1331 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1331
def independentCachedBranchMembers1333 : Finset ℕ := ([1686,1708,1752,2652,2662,2730,2788,3158,3180,3226,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1333 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1333 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1333 4 (fun x => (if x<2730 then (if x<1752 then (if x<1708 then 0 else 0) else (if x<2652 then 0 else (if x<2662 then 1 else 1))) else (if x<3180 then (if x<2788 then 2 else (if x<3158 then 2 else 1)) else (if x<3226 then 1 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1334 : Finset ℕ := ([48,252,1594,1614,1652,1686,1708,1752,2620,2652,2662,2674,2730,2762,2788,2800,3126,3158,3180,3192,3214,3226,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1334 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1334 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1334 48 4
  · have he : independentCachedBranchMembers1334.erase 48=independentCachedBranchMembers1332 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1332
  · have he : independentCachedBranchMembers1334.filter (independentCachedEdge 48)=independentCachedBranchMembers1333 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1333
def independentCachedBranchMembers1335 : Finset ℕ := ([1594,1614,1708,1752,2620,2662,2730,2800,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1335 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1335 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1335 4 (fun x => (if x<2730 then (if x<1752 then (if x<1614 then 0 else (if x<1708 then 0 else 0)) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<2800 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1336 : Finset ℕ := ([48,252,1594,1614,1652,1686,1708,1740,1752,2620,2652,2662,2674,2730,2762,2788,2800,3126,3158,3180,3192,3214,3226,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1336 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1336 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1336 1740 4
  · have he : independentCachedBranchMembers1336.erase 1740=independentCachedBranchMembers1334 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1334
  · have he : independentCachedBranchMembers1336.filter (independentCachedEdge 1740)=independentCachedBranchMembers1335 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1335
def independentCachedBranchMembers1337 : Finset ℕ := ([1594,1614,1708,1752,2652,2674,2762,2788,3126,3180,3214,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1337 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1337 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1337 4 (fun x => (if x<2762 then (if x<1752 then (if x<1614 then 0 else (if x<1708 then 0 else 0)) else (if x<2652 then 0 else (if x<2674 then 1 else 1))) else (if x<3180 then (if x<2788 then 1 else (if x<3126 then 1 else 2)) else (if x<3214 then 2 else (if x<3284 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1338 : Finset ℕ := ([48,252,1594,1614,1652,1686,1708,1720,1740,1752,2620,2652,2662,2674,2730,2762,2788,2800,3126,3158,3180,3192,3214,3226,3252,3284] : List ℕ).toFinset
theorem independentCachedBranchBound1338 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1338 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1338 1720 4
  · have he : independentCachedBranchMembers1338.erase 1720=independentCachedBranchMembers1336 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1336
  · have he : independentCachedBranchMembers1338.filter (independentCachedEdge 1720)=independentCachedBranchMembers1337 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1337
def independentCachedBranchMembers1339 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2652,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800,3102,3126,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1339 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1339 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1339 2786 5
  · have he : independentCachedBranchMembers1339.erase 2786=independentCachedBranchMembers1329 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1329
  · have he : independentCachedBranchMembers1339.filter (independentCachedEdge 2786)=independentCachedBranchMembers1338 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1338
def independentCachedBranchMembers1340 : Finset ℕ := ([12,48,192,252,1596,1686,1720,1740,1776,2618,2638,2652,2674,2732,2762,2776,2788,3126,3180,3214,3228,3250,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1340 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1340 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1340 5 (fun x => (if x<2674 then (if x<1720 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1596 then 0 else (if x<1686 then 0 else 1))) else (if x<2618 then (if x<1740 then 1 else (if x<1776 then 0 else 0)) else (if x<2638 then 2 else (if x<2652 then 2 else 3)))) else (if x<3180 then (if x<2776 then (if x<2732 then 3 else (if x<2762 then 2 else 3)) else (if x<2788 then 2 else (if x<3126 then 3 else 4))) else (if x<3250 then (if x<3214 then 4 else (if x<3228 then 4 else 1)) else (if x<3284 then (if x<3270 then 1 else 1) else (if x<3304 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1341 : Finset ℕ := ([12,192,1596,1776,2618,2638,2732,2776,3228,3250,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1341 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1341 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1341 4 (fun x => (if x<2732 then (if x<1776 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3250 then (if x<2776 then 1 else (if x<3228 then 1 else 2)) else (if x<3270 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1342 : Finset ℕ := ([12,48,192,252,1596,1652,1686,1720,1740,1776,2618,2638,2652,2674,2732,2762,2776,2788,3126,3180,3214,3228,3250,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1342 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1342 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1342 1652 4
  · have he : independentCachedBranchMembers1342.erase 1652=independentCachedBranchMembers1340 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1340
  · have he : independentCachedBranchMembers1342.filter (independentCachedEdge 1652)=independentCachedBranchMembers1341 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1341
def independentCachedBranchMembers1343 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2618,2620,2638,2650,2652,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800,3102,3126,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1343 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1343 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1343 2650 5
  · have he : independentCachedBranchMembers1343.erase 2650=independentCachedBranchMembers1339 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1339
  · have he : independentCachedBranchMembers1343.filter (independentCachedEdge 2650)=independentCachedBranchMembers1342 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1342
def independentCachedBranchMembers1344 : Finset ℕ := ([48,252,1628,1650,1686,1720,1738,1764,2618,2620,2638,2662,2730,2732,2776,2800,3158,3192,3226,3228,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1344 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1344 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1344 5 (fun x => (if x<2730 then (if x<1738 then (if x<1650 then (if x<252 then 0 else (if x<1628 then 0 else 1)) else (if x<1686 then 1 else (if x<1720 then 1 else 0))) else (if x<2620 then (if x<1764 then 1 else (if x<2618 then 1 else 2)) else (if x<2638 then 0 else (if x<2662 then 2 else 3)))) else (if x<3226 then (if x<2800 then (if x<2732 then 3 else (if x<2776 then 2 else 2)) else (if x<3158 then 0 else (if x<3192 then 3 else 0))) else (if x<3252 then (if x<3228 then 3 else (if x<3250 then 4 else 4)) else (if x<3270 then 0 else (if x<3304 then 4 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1345 : Finset ℕ := ([1628,1650,1738,1764,2620,2662,2730,2800,3158,3192,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1345 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1345 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1345 4 (fun x => (if x<2730 then (if x<1764 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<3192 then (if x<2800 then 1 else (if x<3158 then 1 else 2)) else (if x<3226 then 2 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1346 : Finset ℕ := ([48,252,1628,1650,1686,1720,1738,1740,1764,2618,2620,2638,2662,2730,2732,2776,2800,3158,3192,3226,3228,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1346 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1346 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1346 1740 4
  · have he : independentCachedBranchMembers1346.erase 1740=independentCachedBranchMembers1344 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1344
  · have he : independentCachedBranchMembers1346.filter (independentCachedEdge 1740)=independentCachedBranchMembers1345 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1345
def independentCachedBranchMembers1347 : Finset ℕ := ([1628,1650,1738,1764,2618,2638,2732,2776,3228,3250,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1347 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1347 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1347 4 (fun x => (if x<2732 then (if x<1764 then (if x<1650 then 0 else (if x<1738 then 0 else 0)) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3250 then (if x<2776 then 1 else (if x<3228 then 1 else 2)) else (if x<3270 then 2 else (if x<3304 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1348 : Finset ℕ := ([48,252,1628,1650,1652,1686,1720,1738,1740,1764,2618,2620,2638,2662,2730,2732,2776,2800,3158,3192,3226,3228,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1348 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1348 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1348 1652 4
  · have he : independentCachedBranchMembers1348.erase 1652=independentCachedBranchMembers1346 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1346
  · have he : independentCachedBranchMembers1348.filter (independentCachedEdge 1652)=independentCachedBranchMembers1347 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1347
def independentCachedBranchMembers1349 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2606,2618,2620,2638,2650,2652,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800,3102,3126,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1349 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1349 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1349 2606 5
  · have he : independentCachedBranchMembers1349.erase 2606=independentCachedBranchMembers1343 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1343
  · have he : independentCachedBranchMembers1349.filter (independentCachedEdge 2606)=independentCachedBranchMembers1348 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1348
def independentCachedBranchMembers1350 : Finset ℕ := ([1594,1614,1628,1650,1708,1738,1752,1764,2606,2620,2650,2662,2710,2730,2764,2786,2800,3126,3180,3214,3228,3250,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1350 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1350 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1350 5 (fun x => (if x<2710 then (if x<1752 then (if x<1650 then (if x<1614 then 0 else (if x<1628 then 0 else 1)) else (if x<1708 then 1 else (if x<1738 then 0 else 1))) else (if x<2620 then (if x<1764 then 0 else (if x<2606 then 1 else 0)) else (if x<2650 then 2 else (if x<2662 then 0 else 2)))) else (if x<3180 then (if x<2786 then (if x<2730 then 2 else (if x<2764 then 2 else 0)) else (if x<2800 then 1 else (if x<3126 then 2 else 3))) else (if x<3250 then (if x<3214 then 3 else (if x<3228 then 3 else 4)) else (if x<3284 then (if x<3270 then 4 else 4) else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1351 : Finset ℕ := ([1614,1628,1650,1708,2650,2662,2710,2730,3180,3214,3228,3250] : List ℕ).toFinset
theorem independentCachedBranchBound1351 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1351 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1351 4 (fun x => (if x<2710 then (if x<1708 then (if x<1628 then 0 else (if x<1650 then 1 else 0)) else (if x<2650 then 1 else (if x<2662 then 0 else 0))) else (if x<3214 then (if x<2730 then 2 else (if x<3180 then 1 else 2)) else (if x<3228 then 2 else (if x<3250 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1352 : Finset ℕ := ([192,1594,1614,1628,1650,1708,1738,1752,1764,2606,2620,2650,2662,2710,2730,2764,2786,2800,3126,3180,3214,3228,3250,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1352 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1352 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1352 192 4
  · have he : independentCachedBranchMembers1352.erase 192=independentCachedBranchMembers1350 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1350
  · have he : independentCachedBranchMembers1352.filter (independentCachedEdge 192)=independentCachedBranchMembers1351 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1351
def independentCachedBranchMembers1353 : Finset ℕ := ([1594,1738,1752,1764,2650,2662,2710,2730,3126,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1353 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1353 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1353 4 (fun x => (if x<2710 then (if x<1764 then (if x<1738 then 0 else (if x<1752 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 0 else 1))) else (if x<3270 then (if x<2730 then 2 else (if x<3126 then 0 else 2)) else (if x<3284 then 2 else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1354 : Finset ℕ := ([12,192,1594,1614,1628,1650,1708,1738,1752,1764,2606,2620,2650,2662,2710,2730,2764,2786,2800,3126,3180,3214,3228,3250,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1354 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1354 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1354 12 4
  · have he : independentCachedBranchMembers1354.erase 12=independentCachedBranchMembers1352 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1352
  · have he : independentCachedBranchMembers1354.filter (independentCachedEdge 12)=independentCachedBranchMembers1353 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1353
def independentCachedBranchMembers1355 : Finset ℕ := ([1594,1614,1650,1738,2650,2662,2710,2730,3126,3214,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1355 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1355 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1355 4 (fun x => (if x<2710 then (if x<1738 then (if x<1614 then 0 else (if x<1650 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 0 else 2))) else (if x<3214 then (if x<2730 then 2 else (if x<3126 then 2 else 1)) else (if x<3250 then 1 else (if x<3270 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1356 : Finset ℕ := ([1594,1614,2662,2730,3126,3214] : List ℕ).toFinset
theorem independentCachedBranchBound1356 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1356 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1356 3 (fun x => (if x<2730 then (if x<1614 then 0 else (if x<2662 then 0 else 1)) else (if x<3126 then 1 else (if x<3214 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1357 : Finset ℕ := ([1594,1614,1650,1738,2650,2662,2710,2730,2786,3126,3214,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1357 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1357 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1357 2786 3
  · have he : independentCachedBranchMembers1357.erase 2786=independentCachedBranchMembers1355 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1355
  · have he : independentCachedBranchMembers1357.filter (independentCachedEdge 2786)=independentCachedBranchMembers1356 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1356
def independentCachedBranchMembers1358 : Finset ℕ := ([1650,1738,2662,2730,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1358 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1358 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1358 3 (fun x => (if x<2730 then (if x<1738 then 0 else (if x<2662 then 0 else 1)) else (if x<3250 then 1 else (if x<3270 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1359 : Finset ℕ := ([1594,1614,1650,1738,2606,2650,2662,2710,2730,2786,3126,3214,3250,3270] : List ℕ).toFinset
theorem independentCachedBranchBound1359 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1359 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1359 2606 3
  · have he : independentCachedBranchMembers1359.erase 2606=independentCachedBranchMembers1357 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1357
  · have he : independentCachedBranchMembers1359.filter (independentCachedEdge 2606)=independentCachedBranchMembers1358 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1358
def independentCachedBranchMembers1360 : Finset ℕ := ([12,192,252,1594,1614,1628,1650,1708,1738,1752,1764,2606,2620,2650,2662,2710,2730,2764,2786,2800,3126,3180,3214,3228,3250,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1360 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1360 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1360 252 4
  · have he : independentCachedBranchMembers1360.erase 252=independentCachedBranchMembers1354 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1354
  · have he : independentCachedBranchMembers1360.filter (independentCachedEdge 252)=independentCachedBranchMembers1359 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1359
def independentCachedBranchMembers1361 : Finset ℕ := ([1628,1708,1752,1764,2650,2662,2710,2730,2786,3180,3228,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1361 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1361 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1361 4 (fun x => (if x<2710 then (if x<1764 then (if x<1708 then 0 else (if x<1752 then 0 else 1)) else (if x<2650 then 1 else (if x<2662 then 0 else 1))) else (if x<3180 then (if x<2730 then 2 else (if x<2786 then 0 else 2)) else (if x<3284 then (if x<3228 then 3 else 2) else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1362 : Finset ℕ := ([1628,1764,2662,2730,3228,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1362 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1362 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1362 3 (fun x => (if x<2730 then (if x<1764 then 0 else (if x<2662 then 0 else 1)) else (if x<3228 then 1 else (if x<3304 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1363 : Finset ℕ := ([1628,1708,1752,1764,2606,2650,2662,2710,2730,2786,3180,3228,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1363 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1363 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1363 2606 3
  · have he : independentCachedBranchMembers1363.erase 2606=independentCachedBranchMembers1361 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1361
  · have he : independentCachedBranchMembers1363.filter (independentCachedEdge 2606)=independentCachedBranchMembers1362 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1362
def independentCachedBranchMembers1364 : Finset ℕ := ([12,48,192,252,1594,1614,1628,1650,1708,1738,1752,1764,2606,2620,2650,2662,2710,2730,2764,2786,2800,3126,3180,3214,3228,3250,3270,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1364 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1364 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1364 48 4
  · have he : independentCachedBranchMembers1364.erase 48=independentCachedBranchMembers1360 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1360
  · have he : independentCachedBranchMembers1364.filter (independentCachedEdge 48)=independentCachedBranchMembers1363 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1363
def independentCachedBranchMembers1365 : Finset ℕ := ([12,48,192,252,1594,1596,1614,1626,1628,1650,1652,1686,1708,1720,1738,1740,1752,1764,1776,2606,2618,2620,2638,2650,2652,2662,2674,2710,2730,2732,2762,2764,2776,2786,2788,2800,3102,3126,3158,3178,3180,3192,3214,3226,3228,3238,3250,3252,3270,3282,3284,3304] : List ℕ).toFinset
theorem independentCachedBranchBound1365 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1365 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1365 1626 5
  · have he : independentCachedBranchMembers1365.erase 1626=independentCachedBranchMembers1349 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1349
  · have he : independentCachedBranchMembers1365.filter (independentCachedEdge 1626)=independentCachedBranchMembers1364 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1364
def independentCachedBranchMembers1366 : Finset ℕ := ([12,18,48,72,132,192,222,252,1590,1594,1596,1614,1626,1628,1642,1644,1650,1652,1678,1686,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3150,3158,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound1366 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1366 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1366 3222 6
  · have he : independentCachedBranchMembers1366.erase 3222=independentCachedBranchMembers1238 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1238
  · have he : independentCachedBranchMembers1366.filter (independentCachedEdge 3222)=independentCachedBranchMembers1365 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1365
def independentCachedBranchMembers1367 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1740,1776,2614,2620,2650,2668,2702,2772,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1367 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1367 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1367 6 (fun x => (if x<2772 then (if x<1740 then (if x<252 then (if x<48 then 0 else (if x<192 then 0 else 0)) else (if x<1626 then (if x<1596 then 0 else 0) else (if x<1652 then 1 else 1))) else (if x<2620 then (if x<1776 then 0 else (if x<2614 then 0 else 2)) else (if x<2668 then (if x<2650 then 3 else 2) else (if x<2702 then 2 else 2)))) else (if x<3192 then (if x<3130 then (if x<2800 then 2 else (if x<3102 then 3 else 3)) else (if x<3164 then (if x<3150 then 4 else 4) else (if x<3186 then 1 else 1))) else (if x<3274 then (if x<3244 then 3 else (if x<3252 then 4 else 1)) else (if x<3288 then (if x<3282 then 5 else 3) else (if x<3300 then 4 else 5))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1368 : Finset ℕ := ([1596,1626,1652,1740,1776,2614,2668,2702,2772,3102,3192,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1368 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1368 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1368 5 (fun x => (if x<2668 then (if x<1740 then (if x<1626 then 0 else (if x<1652 then 0 else 1)) else (if x<1776 then 0 else (if x<2614 then 0 else 1))) else (if x<3102 then (if x<2702 then 1 else (if x<2772 then 1 else 1)) else (if x<3252 then (if x<3192 then 2 else 2) else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1369 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1740,1776,2614,2620,2650,2668,2702,2764,2772,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1369 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1369 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1369 2764 5
  · have he : independentCachedBranchMembers1369.erase 2764=independentCachedBranchMembers1367 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1367
  · have he : independentCachedBranchMembers1369.filter (independentCachedEdge 2764)=independentCachedBranchMembers1368 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1368
def independentCachedBranchMembers1370 : Finset ℕ := ([12,48,1740,1776,2620,2650,2702,2772,3130,3150,3164,3186,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1370 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1370 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1370 5 (fun x => (if x<2772 then (if x<1776 then (if x<48 then 0 else (if x<1740 then 0 else 0)) else (if x<2650 then (if x<2620 then 0 else 1) else (if x<2702 then 1 else 0))) else (if x<3164 then (if x<3130 then 1 else (if x<3150 then 1 else 0)) else (if x<3252 then (if x<3186 then 1 else 0) else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1371 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1740,1768,1776,2614,2620,2650,2668,2702,2764,2772,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1371 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1371 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1371 1768 5
  · have he : independentCachedBranchMembers1371.erase 1768=independentCachedBranchMembers1369 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1369
  · have he : independentCachedBranchMembers1371.filter (independentCachedEdge 1768)=independentCachedBranchMembers1370 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1370
def independentCachedBranchMembers1372 : Finset ℕ := ([12,252,1596,1740,2614,2650,2668,2800,3102,3164,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1372 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1372 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1372 5 (fun x => (if x<2800 then (if x<1740 then (if x<252 then 0 else (if x<1596 then 0 else 0)) else (if x<2650 then (if x<2614 then 0 else 1) else (if x<2668 then 1 else 0))) else (if x<3186 then (if x<3102 then 1 else (if x<3164 then 1 else 0)) else (if x<3252 then (if x<3244 then 1 else 0) else (if x<3288 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1373 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1734,1740,1768,1776,2614,2620,2650,2668,2702,2764,2772,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1373 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1373 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1373 1734 5
  · have he : independentCachedBranchMembers1373.erase 1734=independentCachedBranchMembers1371 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1371
  · have he : independentCachedBranchMembers1373.filter (independentCachedEdge 1734)=independentCachedBranchMembers1372 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1372
def independentCachedBranchMembers1374 : Finset ℕ := ([192,252,1740,1776,2620,2650,2702,2772,3102,3192,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1374 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1374 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1374 5 (fun x => (if x<2772 then (if x<1776 then (if x<252 then 0 else (if x<1740 then 0 else 0)) else (if x<2650 then (if x<2620 then 0 else 1) else (if x<2702 then 1 else 1))) else (if x<3244 then (if x<3102 then 0 else (if x<3192 then 1 else 1)) else (if x<3288 then (if x<3274 then 1 else 1) else (if x<3300 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1375 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1714,1734,1740,1768,1776,2614,2620,2650,2668,2702,2764,2772,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1375 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1375 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1375 1714 5
  · have he : independentCachedBranchMembers1375.erase 1714=independentCachedBranchMembers1373 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1373
  · have he : independentCachedBranchMembers1375.filter (independentCachedEdge 1714)=independentCachedBranchMembers1374 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1374
def independentCachedBranchMembers1376 : Finset ℕ := ([48,192,1596,1740,2614,2650,2668,2800,3130,3150,3192,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1376 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1376 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1376 5 (fun x => (if x<2800 then (if x<1740 then (if x<192 then 0 else (if x<1596 then 0 else 0)) else (if x<2650 then (if x<2614 then 0 else 0) else (if x<2668 then 1 else 1))) else (if x<3192 then (if x<3130 then 1 else (if x<3150 then 0 else 1)) else (if x<3282 then (if x<3274 then 1 else 0) else (if x<3300 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1377 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1692,1714,1734,1740,1768,1776,2614,2620,2650,2668,2702,2764,2772,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1377 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1377 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1377 1692 5
  · have he : independentCachedBranchMembers1377.erase 1692=independentCachedBranchMembers1375 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1375
  · have he : independentCachedBranchMembers1377.filter (independentCachedEdge 1692)=independentCachedBranchMembers1376 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1376
def independentCachedBranchMembers1378 : Finset ℕ := ([12,48,1596,1626,1652,1714,2614,2668,2764,2800,3130,3150,3164,3186,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1378 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1378 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1378 5 (fun x => (if x<2764 then (if x<1652 then (if x<1596 then (if x<48 then 0 else 0) else (if x<1626 then 0 else 1)) else (if x<2614 then (if x<1714 then 1 else 0) else (if x<2668 then 2 else 2))) else (if x<3164 then (if x<3130 then (if x<2800 then 3 else 2) else (if x<3150 then 3 else 3)) else (if x<3252 then (if x<3186 then 1 else 1) else (if x<3282 then 1 else 4)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1379 : Finset ℕ := ([12,48,3130,3150,3164,3186,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1379 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1379 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1379 4 (fun x => (if x<3164 then (if x<3130 then (if x<48 then 0 else 0) else (if x<3150 then 1 else 0)) else (if x<3252 then (if x<3186 then 1 else 0) else (if x<3282 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1380 : Finset ℕ := ([12,48,1596,1626,1652,1714,1768,2614,2668,2764,2800,3130,3150,3164,3186,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1380 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1380 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1380 1768 4
  · have he : independentCachedBranchMembers1380.erase 1768=independentCachedBranchMembers1378 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1378
  · have he : independentCachedBranchMembers1380.filter (independentCachedEdge 1768)=independentCachedBranchMembers1379 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1379
def independentCachedBranchMembers1381 : Finset ℕ := ([12,1596,2614,2668,2800,3164,3186,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1381 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1381 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1381 4 (fun x => (if x<2800 then (if x<2614 then (if x<1596 then 0 else 0) else (if x<2668 then 1 else 0)) else (if x<3186 then (if x<3164 then 1 else 0) else (if x<3252 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1382 : Finset ℕ := ([12,48,1596,1626,1652,1714,1734,1768,2614,2668,2764,2800,3130,3150,3164,3186,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1382 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1382 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1382 1734 4
  · have he : independentCachedBranchMembers1382.erase 1734=independentCachedBranchMembers1380 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1380
  · have he : independentCachedBranchMembers1382.filter (independentCachedEdge 1734)=independentCachedBranchMembers1381 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1381
def independentCachedBranchMembers1383 : Finset ℕ := ([48,1596,2614,2668,2800,3130,3150,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1383 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1383 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1383 4 (fun x => (if x<2800 then (if x<2614 then (if x<1596 then 0 else 0) else (if x<2668 then 0 else 1)) else (if x<3150 then (if x<3130 then 1 else 0) else (if x<3282 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1384 : Finset ℕ := ([12,48,1596,1626,1652,1692,1714,1734,1768,2614,2668,2764,2800,3130,3150,3164,3186,3252,3282] : List ℕ).toFinset
theorem independentCachedBranchBound1384 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1384 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1384 1692 4
  · have he : independentCachedBranchMembers1384.erase 1692=independentCachedBranchMembers1382 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1382
  · have he : independentCachedBranchMembers1384.filter (independentCachedEdge 1692)=independentCachedBranchMembers1383 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1383
def independentCachedBranchMembers1385 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1692,1714,1734,1740,1768,1776,2614,2620,2650,2668,2702,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1385 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1385 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1385 2792 5
  · have he : independentCachedBranchMembers1385.erase 2792=independentCachedBranchMembers1377 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1377
  · have he : independentCachedBranchMembers1385.filter (independentCachedEdge 2792)=independentCachedBranchMembers1384 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1384
def independentCachedBranchMembers1386 : Finset ℕ := ([12,252,1626,1652,1692,1776,2620,2702,2764,2772,3102,3164,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1386 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1386 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1386 5 (fun x => (if x<2764 then (if x<1692 then (if x<1626 then (if x<252 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<2620 then (if x<1776 then 0 else 0) else (if x<2702 then 2 else 2))) else (if x<3186 then (if x<3102 then (if x<2772 then 3 else 2) else (if x<3164 then 4 else 1)) else (if x<3252 then (if x<3244 then 1 else 3) else (if x<3288 then 1 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1387 : Finset ℕ := ([12,1776,2620,2702,2772,3164,3186,3252] : List ℕ).toFinset
theorem independentCachedBranchBound1387 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1387 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1387 4 (fun x => (if x<2772 then (if x<2620 then (if x<1776 then 0 else 0) else (if x<2702 then 1 else 0)) else (if x<3186 then (if x<3164 then 1 else 1) else (if x<3252 then 0 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1388 : Finset ℕ := ([12,252,1626,1652,1692,1768,1776,2620,2702,2764,2772,3102,3164,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1388 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1388 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1388 1768 4
  · have he : independentCachedBranchMembers1388.erase 1768=independentCachedBranchMembers1386 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1386
  · have he : independentCachedBranchMembers1388.filter (independentCachedEdge 1768)=independentCachedBranchMembers1387 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1387
def independentCachedBranchMembers1389 : Finset ℕ := ([12,252,3102,3164,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1389 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1389 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1389 4 (fun x => (if x<3186 then (if x<3102 then (if x<252 then 0 else 0) else (if x<3164 then 1 else 0)) else (if x<3252 then (if x<3244 then 1 else 0) else (if x<3288 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1390 : Finset ℕ := ([12,252,1626,1652,1692,1734,1768,1776,2620,2702,2764,2772,3102,3164,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1390 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1390 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1390 1734 4
  · have he : independentCachedBranchMembers1390.erase 1734=independentCachedBranchMembers1388 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1388
  · have he : independentCachedBranchMembers1390.filter (independentCachedEdge 1734)=independentCachedBranchMembers1389 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1389
def independentCachedBranchMembers1391 : Finset ℕ := ([252,1776,2620,2702,2772,3102,3244,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1391 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1391 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1391 4 (fun x => (if x<2772 then (if x<2620 then (if x<1776 then 0 else 0) else (if x<2702 then 1 else 1)) else (if x<3244 then (if x<3102 then 0 else 1) else (if x<3288 then 1 else 0))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1392 : Finset ℕ := ([12,252,1626,1652,1692,1714,1734,1768,1776,2620,2702,2764,2772,3102,3164,3186,3244,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound1392 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1392 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1392 1714 4
  · have he : independentCachedBranchMembers1392.erase 1714=independentCachedBranchMembers1390 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1390
  · have he : independentCachedBranchMembers1392.filter (independentCachedEdge 1714)=independentCachedBranchMembers1391 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1391
def independentCachedBranchMembers1393 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1692,1714,1734,1740,1768,1776,2614,2620,2650,2668,2702,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1393 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1393 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1393 2758 5
  · have he : independentCachedBranchMembers1393.erase 2758=independentCachedBranchMembers1385 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1385
  · have he : independentCachedBranchMembers1393.filter (independentCachedEdge 2758)=independentCachedBranchMembers1392 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1392
def independentCachedBranchMembers1394 : Finset ℕ := ([192,252,1596,1626,1652,1734,1768,2614,2668,2764,2800,3102,3192,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1394 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1394 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1394 5 (fun x => (if x<2668 then (if x<1652 then (if x<1596 then (if x<252 then 0 else 0) else (if x<1626 then 0 else 1)) else (if x<1768 then (if x<1734 then 1 else 1) else (if x<2614 then 0 else 2))) else (if x<3192 then (if x<2800 then (if x<2764 then 2 else 3) else (if x<3102 then 2 else 4)) else (if x<3274 then (if x<3244 then 1 else 3) else (if x<3288 then 1 else (if x<3300 then 3 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1395 : Finset ℕ := ([192,252,3102,3192,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1395 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1395 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1395 4 (fun x => (if x<3244 then (if x<3102 then (if x<252 then 0 else 0) else (if x<3192 then 1 else 1)) else (if x<3288 then (if x<3274 then 1 else 1) else (if x<3300 then 0 else 0))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1396 : Finset ℕ := ([192,252,1596,1626,1652,1714,1734,1768,2614,2668,2764,2800,3102,3192,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1396 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1396 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1396 1714 4
  · have he : independentCachedBranchMembers1396.erase 1714=independentCachedBranchMembers1394 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1394
  · have he : independentCachedBranchMembers1396.filter (independentCachedEdge 1714)=independentCachedBranchMembers1395 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1395
def independentCachedBranchMembers1397 : Finset ℕ := ([192,1596,2614,2668,2800,3192,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1397 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1397 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1397 4 (fun x => (if x<2800 then (if x<2614 then (if x<1596 then 0 else 0) else (if x<2668 then 0 else 1)) else (if x<3274 then (if x<3192 then 1 else 1) else (if x<3300 then 0 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1398 : Finset ℕ := ([192,252,1596,1626,1652,1692,1714,1734,1768,2614,2668,2764,2800,3102,3192,3244,3274,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1398 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1398 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1398 1692 4
  · have he : independentCachedBranchMembers1398.erase 1692=independentCachedBranchMembers1396 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1396
  · have he : independentCachedBranchMembers1398.filter (independentCachedEdge 1692)=independentCachedBranchMembers1397 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1397
def independentCachedBranchMembers1399 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1692,1714,1734,1740,1768,1776,2614,2620,2650,2668,2702,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1399 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1399 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1399 2738 5
  · have he : independentCachedBranchMembers1399.erase 2738=independentCachedBranchMembers1393 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1393
  · have he : independentCachedBranchMembers1399.filter (independentCachedEdge 2738)=independentCachedBranchMembers1398 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1398
def independentCachedBranchMembers1400 : Finset ℕ := ([48,192,1626,1652,1734,1768,1776,2620,2702,2764,2772,3130,3150,3192,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1400 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1400 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1400 5 (fun x => (if x<2702 then (if x<1734 then (if x<1626 then (if x<192 then 0 else 0) else (if x<1652 then 1 else 1)) else (if x<1776 then (if x<1768 then 0 else 1) else (if x<2620 then 0 else 2))) else (if x<3150 then (if x<2772 then (if x<2764 then 2 else 3) else (if x<3130 then 2 else 3)) else (if x<3274 then (if x<3192 then 3 else 1) else (if x<3282 then 1 else (if x<3300 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1401 : Finset ℕ := ([192,1776,2620,2702,2772,3192,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1401 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1401 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1401 4 (fun x => (if x<2772 then (if x<2620 then (if x<1776 then 0 else 0) else (if x<2702 then 1 else 1)) else (if x<3274 then (if x<3192 then 0 else 1) else (if x<3300 then 1 else 0))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1402 : Finset ℕ := ([48,192,1626,1652,1714,1734,1768,1776,2620,2702,2764,2772,3130,3150,3192,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1402 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1402 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1402 1714 4
  · have he : independentCachedBranchMembers1402.erase 1714=independentCachedBranchMembers1400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1400
  · have he : independentCachedBranchMembers1402.filter (independentCachedEdge 1714)=independentCachedBranchMembers1401 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1401
def independentCachedBranchMembers1403 : Finset ℕ := ([48,192,3130,3150,3192,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1403 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1403 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1403 4 (fun x => (if x<3192 then (if x<3130 then (if x<192 then 0 else 0) else (if x<3150 then 0 else 1)) else (if x<3282 then (if x<3274 then 1 else 0) else (if x<3300 then 1 else 1))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1404 : Finset ℕ := ([48,192,1626,1652,1692,1714,1734,1768,1776,2620,2702,2764,2772,3130,3150,3192,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1404 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1404 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1404 1692 4
  · have he : independentCachedBranchMembers1404.erase 1692=independentCachedBranchMembers1402 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1402
  · have he : independentCachedBranchMembers1404.filter (independentCachedEdge 1692)=independentCachedBranchMembers1403 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1403
def independentCachedBranchMembers1405 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1692,1714,1734,1740,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1405 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1405 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1405 2716 5
  · have he : independentCachedBranchMembers1405.erase 2716=independentCachedBranchMembers1399 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1399
  · have he : independentCachedBranchMembers1405.filter (independentCachedEdge 2716)=independentCachedBranchMembers1404 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1404
def independentCachedBranchMembers1406 : Finset ℕ := ([12,192,1596,1692,1714,1734,1768,1776,2614,2650,2668,2702,2764,2772,3102,3164,3186,3274,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1406 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1406 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers1406 5 (fun x => (if x<2668 then (if x<1734 then (if x<1596 then (if x<192 then 0 else 0) else (if x<1692 then 0 else (if x<1714 then 1 else 1))) else (if x<1776 then (if x<1768 then 1 else 1) else (if x<2614 then 0 else (if x<2650 then 2 else 2)))) else (if x<3164 then (if x<2764 then (if x<2702 then 2 else 2) else (if x<2772 then 1 else (if x<3102 then 2 else 0))) else (if x<3274 then (if x<3186 then 3 else 3) else (if x<3282 then 3 else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers1407 : Finset ℕ := ([12,48,192,252,1596,1626,1652,1692,1714,1720,1734,1740,1768,1776,2614,2620,2650,2668,2702,2716,2738,2758,2764,2772,2792,2800,3102,3130,3150,3164,3186,3192,3244,3252,3274,3282,3288,3300] : List ℕ).toFinset
theorem independentCachedBranchBound1407 : ListCliqueBound independentCachedEdge independentCachedBranchMembers1407 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers1407 1720 5
  · have he : independentCachedBranchMembers1407.erase 1720=independentCachedBranchMembers1405 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1405
  · have he : independentCachedBranchMembers1407.filter (independentCachedEdge 1720)=independentCachedBranchMembers1406 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound1406
end EntropyDesigns.QuadraticRefinement
