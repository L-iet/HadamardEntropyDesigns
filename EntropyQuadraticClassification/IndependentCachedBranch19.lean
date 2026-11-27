/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch18
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers2432 : Finset ℕ := ([48,192,1596,1614,1686,1714,1740,1764,1768,2614,2618,2668,2740,2758,2786,3102,3126,3180,3252,3256,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2432 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2432 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2432 3252 4
  · have he : independentCachedBranchMembers2432.erase 3252=independentCachedBranchMembers2430 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2430
  · have he : independentCachedBranchMembers2432.filter (independentCachedEdge 3252)=independentCachedBranchMembers2431 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2431
def independentCachedBranchMembers2433 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1644,1686,1692,1714,1720,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3132,3178,3180,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2433 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2433 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2433 1644 5
  · have he : independentCachedBranchMembers2433.erase 1644=independentCachedBranchMembers2429 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2429
  · have he : independentCachedBranchMembers2433.filter (independentCachedEdge 1644)=independentCachedBranchMembers2432 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2432
def independentCachedBranchMembers2434 : Finset ℕ := ([48,72,192,1590,1596,1614,1740,1768,2614,2620,2638,2714,2740,2758,2764,2786,2792,3102,3180,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2434 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2434 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2434 5 (fun x => (if x<2714 then (if x<1614 then (if x<192 then (if x<72 then 0 else 0) else (if x<1590 then 1 else (if x<1596 then 0 else 1))) else (if x<2614 then (if x<1740 then 0 else (if x<1768 then 1 else 2)) else (if x<2620 then 1 else (if x<2638 then 3 else 3)))) else (if x<3102 then (if x<2764 then (if x<2740 then 3 else (if x<2758 then 0 else 1)) else (if x<2786 then 0 else (if x<2792 then 2 else 3))) else (if x<3256 then (if x<3180 then 2 else (if x<3250 then 3 else 0)) else (if x<3274 then 3 else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2435 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1644,1686,1692,1714,1720,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2764,2786,2792,3102,3126,3132,3178,3180,3226,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2435 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2435 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2435 3226 5
  · have he : independentCachedBranchMembers2435.erase 3226=independentCachedBranchMembers2433 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2433
  · have he : independentCachedBranchMembers2435.filter (independentCachedEdge 3226)=independentCachedBranchMembers2434 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2434
def independentCachedBranchMembers2436 : Finset ℕ := ([18,1594,1644,1686,1692,1714,1720,1738,1764,2614,2620,2638,2714,2740,2758,2764,2786,2792,3102,3180,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2436 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2436 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2436 5 (fun x => (if x<2714 then (if x<1720 then (if x<1686 then (if x<1594 then 0 else (if x<1644 then 0 else 0)) else (if x<1692 then 1 else (if x<1714 then 2 else 2))) else (if x<2614 then (if x<1738 then 1 else (if x<1764 then 1 else 1)) else (if x<2620 then 3 else (if x<2638 then 4 else 3)))) else (if x<3102 then (if x<2764 then (if x<2740 then 0 else (if x<2758 then 1 else 1)) else (if x<2786 then 0 else (if x<2792 then 2 else 1))) else (if x<3256 then (if x<3180 then 3 else (if x<3250 then 4 else 0)) else (if x<3274 then 4 else (if x<3300 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2437 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1644,1686,1692,1714,1720,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2740,2758,2762,2764,2786,2792,3102,3126,3132,3178,3180,3226,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2437 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2437 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2437 2762 5
  · have he : independentCachedBranchMembers2437.erase 2762=independentCachedBranchMembers2435 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2435
  · have he : independentCachedBranchMembers2437.filter (independentCachedEdge 2762)=independentCachedBranchMembers2436 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2436
def independentCachedBranchMembers2438 : Finset ℕ := ([192,1596,1714,1738,1764,1768,2614,2618,2638,2668,2714,2740,2764,2786,3102,3132,3178,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2438 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2438 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2438 5 (fun x => (if x<2714 then (if x<1768 then (if x<1714 then (if x<1596 then 0 else 0) else (if x<1738 then 1 else (if x<1764 then 1 else 0))) else (if x<2618 then (if x<2614 then 2 else 1) else (if x<2638 then 0 else (if x<2668 then 1 else 2)))) else (if x<3132 then (if x<2764 then (if x<2740 then 1 else 3) else (if x<2786 then 3 else (if x<3102 then 0 else 0))) else (if x<3270 then (if x<3178 then 4 else (if x<3250 then 2 else 3)) else (if x<3274 then 0 else (if x<3300 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2439 : Finset ℕ := ([192,1596,2614,2618,2638,2668,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2439 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2439 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2439 4 (fun x => (if x<2668 then (if x<2614 then (if x<1596 then 0 else 0) else (if x<2618 then 0 else (if x<2638 then 1 else 1))) else (if x<3270 then (if x<3250 then 2 else 1) else (if x<3274 then 1 else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2440 : Finset ℕ := ([192,1596,1692,1714,1738,1764,1768,2614,2618,2638,2668,2714,2740,2764,2786,3102,3132,3178,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2440 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2440 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2440 1692 4
  · have he : independentCachedBranchMembers2440.erase 1692=independentCachedBranchMembers2438 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2438
  · have he : independentCachedBranchMembers2440.filter (independentCachedEdge 1692)=independentCachedBranchMembers2439 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2439
def independentCachedBranchMembers2441 : Finset ℕ := ([192,1596,1738,1764,2614,2668,2714,2740,3132,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2441 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2441 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2441 4 (fun x => (if x<2668 then (if x<1738 then (if x<1596 then 0 else 0) else (if x<1764 then 1 else (if x<2614 then 0 else 1))) else (if x<3132 then (if x<2714 then 2 else (if x<2740 then 1 else 2)) else (if x<3274 then 2 else (if x<3300 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2442 : Finset ℕ := ([192,1596,1692,1714,1738,1764,1768,2614,2618,2638,2668,2710,2714,2740,2764,2786,3102,3132,3178,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2442 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2442 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2442 2710 4
  · have he : independentCachedBranchMembers2442.erase 2710=independentCachedBranchMembers2440 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2440
  · have he : independentCachedBranchMembers2442.filter (independentCachedEdge 2710)=independentCachedBranchMembers2441 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2441
def independentCachedBranchMembers2443 : Finset ℕ := ([1596,1692,1714,1768,2618,2638,2714,2740,3102,3178,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2443 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2443 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2443 4 (fun x => (if x<2714 then (if x<1768 then (if x<1692 then 0 else (if x<1714 then 1 else 0)) else (if x<2618 then 0 else (if x<2638 then 2 else 2))) else (if x<3178 then (if x<2740 then 1 else (if x<3102 then 1 else 2)) else (if x<3274 then 2 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2444 : Finset ℕ := ([192,1596,1692,1714,1738,1764,1768,2614,2618,2638,2668,2710,2714,2740,2764,2786,3102,3132,3178,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2444 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2444 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2444 3304 4
  · have he : independentCachedBranchMembers2444.erase 3304=independentCachedBranchMembers2442 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2442
  · have he : independentCachedBranchMembers2444.filter (independentCachedEdge 3304)=independentCachedBranchMembers2443 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2443
def independentCachedBranchMembers2445 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1644,1686,1692,1714,1720,1738,1740,1764,1768,2614,2618,2620,2638,2668,2710,2714,2738,2740,2758,2762,2764,2786,2792,3102,3126,3132,3178,3180,3226,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2445 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2445 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2445 2738 5
  · have he : independentCachedBranchMembers2445.erase 2738=independentCachedBranchMembers2437 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2437
  · have he : independentCachedBranchMembers2445.filter (independentCachedEdge 2738)=independentCachedBranchMembers2444 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2444
def independentCachedBranchMembers2446 : Finset ℕ := ([18,48,72,192,1594,1596,1686,1714,1738,1740,1768,2614,2638,2668,2714,2758,2786,3102,3132,3250,3252,3274,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2446 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2446 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2446 5 (fun x => (if x<2638 then (if x<1686 then (if x<192 then (if x<48 then 0 else (if x<72 then 1 else 0)) else (if x<1594 then 1 else (if x<1596 then 1 else 2))) else (if x<1740 then (if x<1714 then 0 else (if x<1738 then 2 else 1)) else (if x<1768 then 0 else (if x<2614 then 2 else 0)))) else (if x<3132 then (if x<2758 then (if x<2668 then 3 else (if x<2714 then 0 else 3)) else (if x<2786 then 1 else (if x<3102 then 2 else 3))) else (if x<3274 then (if x<3250 then 1 else (if x<3252 then 0 else 4)) else (if x<3276 then 3 else (if x<3304 then 1 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2447 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1644,1686,1692,1714,1720,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2738,2740,2758,2762,2764,2786,2792,3102,3126,3132,3178,3180,3226,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2447 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2447 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2447 2662 5
  · have he : independentCachedBranchMembers2447.erase 2662=independentCachedBranchMembers2445 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2445
  · have he : independentCachedBranchMembers2447.filter (independentCachedEdge 2662)=independentCachedBranchMembers2446 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2446
def independentCachedBranchMembers2448 : Finset ℕ := ([18,72,1594,1614,1686,1720,1738,1740,1764,2714,2738,2740,2758,2792,3102,3126,3178,3180,3226,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2448 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2448 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2448 5 (fun x => (if x<2740 then (if x<1720 then (if x<1594 then (if x<72 then 0 else 0) else (if x<1614 then 1 else (if x<1686 then 1 else 0))) else (if x<1764 then (if x<1738 then 2 else (if x<1740 then 2 else 0)) else (if x<2714 then 2 else (if x<2738 then 2 else 0)))) else (if x<3180 then (if x<3102 then (if x<2758 then 2 else (if x<2792 then 1 else 0)) else (if x<3126 then 3 else (if x<3178 then 0 else 3))) else (if x<3252 then (if x<3226 then 0 else (if x<3250 then 4 else 3)) else (if x<3270 then 4 else (if x<3304 then 3 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2449 : Finset ℕ := ([1594,1720,1738,2714,2738,2792,3102,3126,3180,3252,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2449 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2449 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2449 4 (fun x => (if x<2792 then (if x<1738 then (if x<1720 then 0 else 1) else (if x<2714 then 0 else (if x<2738 then 0 else 1))) else (if x<3180 then (if x<3102 then 1 else (if x<3126 then 2 else 3)) else (if x<3252 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2450 : Finset ℕ := ([18,72,1594,1614,1686,1720,1738,1740,1764,2668,2714,2738,2740,2758,2792,3102,3126,3178,3180,3226,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2450 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2450 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2450 2668 4
  · have he : independentCachedBranchMembers2450.erase 2668=independentCachedBranchMembers2448 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2448
  · have he : independentCachedBranchMembers2450.filter (independentCachedEdge 2668)=independentCachedBranchMembers2449 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2449
def independentCachedBranchMembers2451 : Finset ℕ := ([1614,1720,1764,2738,2740,2792,3126,3178,3180,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2451 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2451 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2451 4 (fun x => (if x<2792 then (if x<1764 then (if x<1720 then 0 else 1) else (if x<2738 then 0 else (if x<2740 then 1 else 0))) else (if x<3180 then (if x<3126 then 1 else (if x<3178 then 2 else 2)) else (if x<3226 then 3 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2452 : Finset ℕ := ([18,72,1594,1614,1686,1720,1738,1740,1764,2614,2668,2714,2738,2740,2758,2792,3102,3126,3178,3180,3226,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2452 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2452 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2452 2614 4
  · have he : independentCachedBranchMembers2452.erase 2614=independentCachedBranchMembers2450 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2450
  · have he : independentCachedBranchMembers2452.filter (independentCachedEdge 2614)=independentCachedBranchMembers2451 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2451
def independentCachedBranchMembers2453 : Finset ℕ := ([18,72,1594,1720,1738,2714,2738,2792,3178,3226,3250,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2453 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2453 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2453 4 (fun x => (if x<2738 then (if x<1720 then (if x<72 then 0 else (if x<1594 then 0 else 1)) else (if x<1738 then 2 else (if x<2714 then 1 else 1))) else (if x<3226 then (if x<2792 then 0 else (if x<3178 then 0 else 3)) else (if x<3250 then 2 else (if x<3304 then 3 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2454 : Finset ℕ := ([18,72,1594,1596,1614,1686,1720,1738,1740,1764,2614,2668,2714,2738,2740,2758,2792,3102,3126,3178,3180,3226,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2454 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2454 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2454 1596 4
  · have he : independentCachedBranchMembers2454.erase 1596=independentCachedBranchMembers2452 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2452
  · have he : independentCachedBranchMembers2454.filter (independentCachedEdge 1596)=independentCachedBranchMembers2453 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2453
def independentCachedBranchMembers2455 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1644,1686,1692,1714,1720,1734,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2738,2740,2758,2762,2764,2786,2792,3102,3126,3132,3178,3180,3226,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2455 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2455 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2455 1734 5
  · have he : independentCachedBranchMembers2455.erase 1734=independentCachedBranchMembers2447 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2447
  · have he : independentCachedBranchMembers2455.filter (independentCachedEdge 1734)=independentCachedBranchMembers2454 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2454
def independentCachedBranchMembers2456 : Finset ℕ := ([18,48,192,1594,1614,1644,1686,1692,1738,1768,2614,2620,2714,2738,2758,2764,3102,3126,3132,3178,3226,3250,3256,3270,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2456 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2456 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2456 5 (fun x => (if x<2738 then (if x<1686 then (if x<1594 then (if x<48 then 0 else (if x<192 then 1 else 0)) else (if x<1614 then 0 else (if x<1644 then 1 else 2))) else (if x<1768 then (if x<1692 then 3 else (if x<1738 then 2 else 2)) else (if x<2620 then (if x<2614 then 0 else 0) else (if x<2714 then 2 else 2)))) else (if x<3178 then (if x<3102 then (if x<2758 then 1 else (if x<2764 then 1 else 2)) else (if x<3126 then 0 else (if x<3132 then 3 else 4))) else (if x<3256 then (if x<3226 then 3 else (if x<3250 then 3 else 4)) else (if x<3276 then (if x<3270 then 1 else 3) else (if x<3300 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2457 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1692,1714,1720,1734,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2738,2740,2758,2762,2764,2786,2792,3102,3126,3132,3178,3180,3226,3250,3252,3256,3270,3274,3276,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2457 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2457 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2457 1642 5
  · have he : independentCachedBranchMembers2457.erase 1642=independentCachedBranchMembers2455 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2455
  · have he : independentCachedBranchMembers2457.filter (independentCachedEdge 1642)=independentCachedBranchMembers2456 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2456
def independentCachedBranchMembers2458 : Finset ℕ := ([18,48,72,1590,1594,1614,1644,1686,1720,1740,2614,2618,2638,2668,2710,2714,2740,2764,2786,3102,3132,3178,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2458 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2458 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2458 5 (fun x => (if x<2668 then (if x<1644 then (if x<1590 then (if x<48 then 0 else (if x<72 then 1 else 0)) else (if x<1594 then 0 else (if x<1614 then 1 else 1))) else (if x<1740 then (if x<1686 then 0 else (if x<1720 then 2 else 2)) else (if x<2618 then (if x<2614 then 2 else 3) else (if x<2638 then 4 else 3)))) else (if x<3132 then (if x<2740 then (if x<2710 then 4 else (if x<2714 then 0 else 3)) else (if x<2786 then (if x<2764 then 4 else 0) else (if x<3102 then 3 else 3))) else (if x<3270 then (if x<3178 then 4 else (if x<3250 then 4 else 0)) else (if x<3300 then (if x<3274 then 1 else 3) else (if x<3304 then 4 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2459 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1692,1714,1720,1734,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2738,2740,2758,2762,2764,2786,2792,3102,3126,3132,3178,3180,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2459 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2459 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2459 3298 5
  · have he : independentCachedBranchMembers2459.erase 3298=independentCachedBranchMembers2457 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2457
  · have he : independentCachedBranchMembers2459.filter (independentCachedEdge 3298)=independentCachedBranchMembers2458 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2458
def independentCachedBranchMembers2460 : Finset ℕ := ([48,192,1594,1596,1614,1686,1720,1738,1740,1764,2618,2620,2638,2662,2710,2762,2764,2786,3102,3126,3178,3180,3226,3250,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2460 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2460 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2460 5 (fun x => (if x<2662 then (if x<1720 then (if x<1596 then (if x<192 then 0 else (if x<1594 then 0 else 0)) else (if x<1614 then 1 else (if x<1686 then 1 else 1))) else (if x<1764 then (if x<1738 then 2 else (if x<1740 then 0 else 2)) else (if x<2620 then (if x<2618 then 1 else 2) else (if x<2638 then 0 else 2)))) else (if x<3178 then (if x<2764 then (if x<2710 then 3 else (if x<2762 then 3 else 3)) else (if x<3102 then (if x<2786 then 0 else 4) else (if x<3126 then 1 else 0))) else (if x<3250 then (if x<3180 then 3 else (if x<3226 then 1 else 3)) else (if x<3270 then (if x<3252 then 2 else 1) else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2461 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1692,1714,1720,1734,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2738,2740,2758,2762,2764,2786,2792,3102,3126,3132,3178,3180,3222,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2461 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2461 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2461 3222 5
  · have he : independentCachedBranchMembers2461.erase 3222=independentCachedBranchMembers2459 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2459
  · have he : independentCachedBranchMembers2461.filter (independentCachedEdge 3222)=independentCachedBranchMembers2460 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2460
def independentCachedBranchMembers2462 : Finset ℕ := ([72,1594,1614,1644,1686,1692,1738,1768,2618,2638,2662,2668,2710,2740,2762,2786,2792,3102,3126,3132,3178,3226,3250,3256,3270,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2462 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2462 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2462 5 (fun x => (if x<2740 then (if x<1738 then (if x<1644 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1686 then 1 else (if x<1692 then 0 else 1))) else (if x<2638 then (if x<1768 then 1 else (if x<2618 then 2 else 3)) else (if x<2668 then (if x<2662 then 3 else 4) else (if x<2710 then 0 else 2)))) else (if x<3178 then (if x<2792 then (if x<2762 then 0 else (if x<2786 then 2 else 3)) else (if x<3126 then (if x<3102 then 4 else 3) else (if x<3132 then 2 else 1))) else (if x<3256 then (if x<3226 then 0 else (if x<3250 then 1 else 0)) else (if x<3276 then (if x<3270 then 4 else 3) else (if x<3300 then 1 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2463 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1692,1714,1720,1734,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2738,2740,2758,2762,2764,2786,2792,3102,3126,3130,3132,3178,3180,3222,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2463 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2463 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2463 3130 5
  · have he : independentCachedBranchMembers2463.erase 3130=independentCachedBranchMembers2461 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2461
  · have he : independentCachedBranchMembers2463.filter (independentCachedEdge 3130)=independentCachedBranchMembers2462 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2462
def independentCachedBranchMembers2464 : Finset ℕ := ([48,72,1590,1614,1686,1692,1714,1720,1738,1764,2618,2662,2668,2714,2740,2758,2764,2786,2792,3126,3132,3178,3222,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2464 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2464 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2464 5 (fun x => (if x<2714 then (if x<1714 then (if x<1614 then (if x<72 then 0 else (if x<1590 then 0 else 0)) else (if x<1686 then 0 else (if x<1692 then 1 else 2))) else (if x<1764 then (if x<1720 then 2 else (if x<1738 then 1 else 1)) else (if x<2662 then (if x<2618 then 1 else 3) else (if x<2668 then 3 else 4)))) else (if x<3132 then (if x<2764 then (if x<2740 then 1 else (if x<2758 then 0 else 1)) else (if x<2792 then (if x<2786 then 0 else 2) else (if x<3126 then 1 else 3))) else (if x<3250 then (if x<3178 then 4 else (if x<3222 then 3 else 4)) else (if x<3274 then (if x<3256 then 0 else 3) else (if x<3300 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2465 : Finset ℕ := ([48,1614,1692,1738,2714,2758,2764,3126,3132,3178,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2465 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2465 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2465 4 (fun x => (if x<2764 then (if x<1738 then (if x<1614 then 0 else (if x<1692 then 0 else 1)) else (if x<2714 then 1 else (if x<2758 then 1 else 0))) else (if x<3178 then (if x<3126 then 1 else (if x<3132 then 2 else 3)) else (if x<3256 then (if x<3250 then 2 else 3) else (if x<3300 then 0 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2466 : Finset ℕ := ([48,1692,2764,3132,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2466 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2466 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2466 3 (fun x => (if x<3132 then (if x<1692 then 0 else (if x<2764 then 1 else 0)) else (if x<3256 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2467 : Finset ℕ := ([48,1614,1686,1692,1738,2714,2758,2764,3126,3132,3178,3250,3256,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2467 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2467 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2467 1686 3
  · have he : independentCachedBranchMembers2467.erase 1686=independentCachedBranchMembers2465 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2465
  · have he : independentCachedBranchMembers2467.filter (independentCachedEdge 1686)=independentCachedBranchMembers2466 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2466
def independentCachedBranchMembers2468 : Finset ℕ := ([48,72,1590,1614,1642,1686,1692,1714,1720,1738,1764,2618,2662,2668,2714,2740,2758,2764,2786,2792,3126,3132,3178,3222,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2468 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2468 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2468 1642 4
  · have he : independentCachedBranchMembers2468.erase 1642=independentCachedBranchMembers2464 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2464
  · have he : independentCachedBranchMembers2468.filter (independentCachedEdge 1642)=independentCachedBranchMembers2467 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2467
def independentCachedBranchMembers2469 : Finset ℕ := ([1590,1692,1720,1738,2662,2714,2764,2792,3132,3178,3222,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2469 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2469 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2469 4 (fun x => (if x<2764 then (if x<1738 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2662 then 1 else (if x<2714 then 0 else 1))) else (if x<3178 then (if x<2792 then 0 else (if x<3132 then 1 else 2)) else (if x<3250 then (if x<3222 then 2 else 3) else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2470 : Finset ℕ := ([1692,1720,2662,2714,3132,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2470 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2470 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2470 3 (fun x => (if x<2714 then (if x<1720 then 0 else (if x<2662 then 1 else 0)) else (if x<3132 then 1 else (if x<3300 then 2 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2471 : Finset ℕ := ([72,1590,1692,1720,1738,2662,2714,2764,2792,3132,3178,3222,3250,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2471 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2471 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2471 72 3
  · have he : independentCachedBranchMembers2471.erase 72=independentCachedBranchMembers2469 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2469
  · have he : independentCachedBranchMembers2471.filter (independentCachedEdge 72)=independentCachedBranchMembers2470 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2470
def independentCachedBranchMembers2472 : Finset ℕ := ([48,72,1590,1596,1614,1642,1686,1692,1714,1720,1738,1764,2618,2662,2668,2714,2740,2758,2764,2786,2792,3126,3132,3178,3222,3250,3256,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2472 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2472 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2472 1596 4
  · have he : independentCachedBranchMembers2472.erase 1596=independentCachedBranchMembers2468 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2468
  · have he : independentCachedBranchMembers2472.filter (independentCachedEdge 1596)=independentCachedBranchMembers2471 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2471
def independentCachedBranchMembers2473 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1692,1714,1720,1734,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2738,2740,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3178,3180,3222,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2473 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2473 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2473 2788 5
  · have he : independentCachedBranchMembers2473.erase 2788=independentCachedBranchMembers2463 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2463
  · have he : independentCachedBranchMembers2473.filter (independentCachedEdge 2788)=independentCachedBranchMembers2472 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2472
def independentCachedBranchMembers2474 : Finset ℕ := ([18,48,72,192,1590,1594,1644,1692,1714,1734,1738,1768,2620,2662,2710,2714,2740,2764,2786,3126,3180,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2474 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2474 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2474 5 (fun x => (if x<2620 then (if x<1644 then (if x<192 then (if x<48 then 0 else (if x<72 then 1 else 0)) else (if x<1590 then 1 else (if x<1594 then 0 else 1))) else (if x<1734 then (if x<1692 then 0 else (if x<1714 then 2 else 2)) else (if x<1738 then 2 else (if x<1768 then 1 else 2)))) else (if x<2786 then (if x<2714 then (if x<2662 then 1 else (if x<2710 then 3 else 0)) else (if x<2740 then 4 else (if x<2764 then 3 else 0))) else (if x<3250 then (if x<3126 then 2 else (if x<3180 then 1 else 4)) else (if x<3274 then (if x<3270 then 0 else 1) else (if x<3300 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2475 : Finset ℕ := ([48,72,1594,1644,1734,1768,2620,2710,3126,3250,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2475 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2475 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2475 4 (fun x => (if x<2620 then (if x<1644 then (if x<72 then 0 else (if x<1594 then 0 else 1)) else (if x<1734 then 1 else (if x<1768 then 2 else 2))) else (if x<3250 then (if x<2710 then 1 else (if x<3126 then 2 else 0)) else (if x<3274 then 3 else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2476 : Finset ℕ := ([18,48,72,192,1590,1594,1644,1692,1714,1734,1738,1764,1768,2620,2662,2710,2714,2740,2764,2786,3126,3180,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2476 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2476 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2476 1764 4
  · have he : independentCachedBranchMembers2476.erase 1764=independentCachedBranchMembers2474 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2474
  · have he : independentCachedBranchMembers2476.filter (independentCachedEdge 1764)=independentCachedBranchMembers2475 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2475
def independentCachedBranchMembers2477 : Finset ℕ := ([18,192,1644,1714,1734,1738,2620,2710,2714,2786,3126,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2477 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2477 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2477 4 (fun x => (if x<2620 then (if x<1714 then (if x<192 then 0 else (if x<1644 then 0 else 1)) else (if x<1734 then 2 else (if x<1738 then 1 else 2))) else (if x<2786 then (if x<2710 then 1 else (if x<2714 then 1 else 2)) else (if x<3126 then 2 else (if x<3300 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2478 : Finset ℕ := ([18,48,72,192,1590,1594,1614,1644,1692,1714,1734,1738,1764,1768,2620,2662,2710,2714,2740,2764,2786,3126,3180,3250,3270,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2478 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2478 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2478 1614 4
  · have he : independentCachedBranchMembers2478.erase 1614=independentCachedBranchMembers2476 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2476
  · have he : independentCachedBranchMembers2478.filter (independentCachedEdge 1614)=independentCachedBranchMembers2477 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2477
def independentCachedBranchMembers2479 : Finset ℕ := ([48,1594,1614,1692,1714,1734,1768,2620,2662,2714,2740,3126,3180,3274,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2479 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2479 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2479 4 (fun x => (if x<2620 then (if x<1692 then (if x<1594 then 0 else (if x<1614 then 0 else 0)) else (if x<1734 then (if x<1714 then 1 else 1) else (if x<1768 then 1 else 1))) else (if x<3126 then (if x<2714 then (if x<2662 then 2 else 2) else (if x<2740 then 3 else 3)) else (if x<3274 then (if x<3180 then 2 else 2) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2480 : Finset ℕ := ([18,48,72,192,1590,1594,1614,1644,1692,1714,1734,1738,1764,1768,2620,2662,2710,2714,2740,2764,2786,3126,3180,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2480 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2480 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2480 3304 4
  · have he : independentCachedBranchMembers2480.erase 3304=independentCachedBranchMembers2478 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2478
  · have he : independentCachedBranchMembers2480.filter (independentCachedEdge 3304)=independentCachedBranchMembers2479 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2479
def independentCachedBranchMembers2481 : Finset ℕ := ([72,1594,1614,1644,1692,1738,1768,2662,2710,2740,2786,3126,3250,3270,3300] : List ℕ).toFinset
theorem independentCachedBranchBound2481 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2481 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2481 4 (fun x => (if x<2662 then (if x<1644 then (if x<1594 then 0 else (if x<1614 then 1 else 0)) else (if x<1738 then (if x<1692 then 1 else 1) else (if x<1768 then 1 else 0))) else (if x<3126 then (if x<2740 then (if x<2710 then 2 else 2) else (if x<2786 then 3 else 3)) else (if x<3270 then (if x<3250 then 2 else 3) else (if x<3300 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2482 : Finset ℕ := ([18,48,72,192,1590,1594,1614,1644,1692,1714,1734,1738,1764,1768,2620,2662,2710,2714,2740,2764,2786,3126,3130,3180,3250,3270,3274,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2482 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2482 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2482 3130 4
  · have he : independentCachedBranchMembers2482.erase 3130=independentCachedBranchMembers2480 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2480
  · have he : independentCachedBranchMembers2482.filter (independentCachedEdge 3130)=independentCachedBranchMembers2481 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2481
def independentCachedBranchMembers2483 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1692,1714,1720,1734,1738,1740,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2716,2738,2740,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3178,3180,3222,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2483 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2483 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2483 2716 5
  · have he : independentCachedBranchMembers2483.erase 2716=independentCachedBranchMembers2473 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2473
  · have he : independentCachedBranchMembers2483.filter (independentCachedEdge 2716)=independentCachedBranchMembers2482 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2482
def independentCachedBranchMembers2484 : Finset ℕ := ([18,48,72,1596,1642,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2710,2714,2740,2764,2786,3126,3130,3180,3222,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2484 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2484 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2484 5 (fun x => (if x<2668 then (if x<1734 then (if x<1596 then (if x<48 then 0 else (if x<72 then 1 else 0)) else (if x<1692 then (if x<1642 then 1 else 2) else (if x<1714 then 3 else 0))) else (if x<1768 then (if x<1738 then 2 else (if x<1764 then 3 else 3)) else (if x<2618 then (if x<2614 then 0 else 0) else (if x<2638 then 1 else 2)))) else (if x<3130 then (if x<2740 then (if x<2710 then 0 else (if x<2714 then 2 else 3)) else (if x<2786 then (if x<2764 then 1 else 3) else (if x<3126 then 2 else 1))) else (if x<3252 then (if x<3180 then 4 else (if x<3222 then 4 else 0)) else (if x<3276 then (if x<3256 then 4 else 1) else (if x<3298 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2485 : Finset ℕ := ([72,1596,1642,1734,1768,2614,2638,2714,2740,2764,2786,3130,3180,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2485 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2485 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2485 4 (fun x => (if x<2714 then (if x<1734 then (if x<1596 then 0 else (if x<1642 then 1 else 0)) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2638 then 1 else 0))) else (if x<3130 then (if x<2764 then (if x<2740 then 3 else 3) else (if x<2786 then 2 else 1)) else (if x<3222 then (if x<3180 then 2 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2486 : Finset ℕ := ([1642,1768,2714,2786,3180,3222] : List ℕ).toFinset
theorem independentCachedBranchBound2486 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2486 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2486 3 (fun x => (if x<2786 then (if x<1768 then 0 else (if x<2714 then 1 else 2)) else (if x<3180 then 0 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2487 : Finset ℕ := ([48,72,1596,1642,1734,1768,2614,2638,2714,2740,2764,2786,3130,3180,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2487 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2487 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2487 48 3
  · have he : independentCachedBranchMembers2487.erase 48=independentCachedBranchMembers2485 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2485
  · have he : independentCachedBranchMembers2487.filter (independentCachedEdge 48)=independentCachedBranchMembers2486 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2486
def independentCachedBranchMembers2488 : Finset ℕ := ([18,48,72,1596,1642,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2710,2714,2740,2764,2786,3126,3130,3180,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2488 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2488 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2488 3226 4
  · have he : independentCachedBranchMembers2488.erase 3226=independentCachedBranchMembers2484 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2484
  · have he : independentCachedBranchMembers2488.filter (independentCachedEdge 3226)=independentCachedBranchMembers2487 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2487
def independentCachedBranchMembers2489 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1692,1714,1720,1734,1738,1740,1762,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2716,2738,2740,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3178,3180,3222,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2489 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2489 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2489 1762 5
  · have he : independentCachedBranchMembers2489.erase 1762=independentCachedBranchMembers2483 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2483
  · have he : independentCachedBranchMembers2489.filter (independentCachedEdge 1762)=independentCachedBranchMembers2488 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2488
def independentCachedBranchMembers2490 : Finset ℕ := ([48,72,1594,1644,1686,1692,1714,1720,1738,1764,2620,2638,2714,2740,2764,2792,3126,3132,3178,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2490 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2490 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2490 5 (fun x => (if x<2714 then (if x<1714 then (if x<1644 then (if x<72 then 0 else (if x<1594 then 0 else 1)) else (if x<1686 then 1 else (if x<1692 then 2 else 1))) else (if x<1764 then (if x<1720 then 0 else (if x<1738 then 2 else 0)) else (if x<2620 then 2 else (if x<2638 then 1 else 0)))) else (if x<3178 then (if x<2792 then (if x<2740 then 1 else (if x<2764 then 2 else 1)) else (if x<3126 then 2 else (if x<3132 then 3 else 4))) else (if x<3270 then (if x<3226 then 3 else (if x<3252 then 3 else 0)) else (if x<3276 then 3 else (if x<3304 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2491 : Finset ℕ := ([48,72,1594,1644,1686,1720,2620,2792,3126,3226,3252,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2491 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2491 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2491 4 (fun x => (if x<2620 then (if x<1644 then (if x<72 then 0 else (if x<1594 then 0 else 1)) else (if x<1686 then 1 else (if x<1720 then 2 else 2))) else (if x<3226 then (if x<2792 then 1 else (if x<3126 then 2 else 0)) else (if x<3252 then 3 else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2492 : Finset ℕ := ([48,72,1594,1644,1686,1692,1714,1720,1738,1764,2620,2638,2714,2740,2764,2786,2792,3126,3132,3178,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2492 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2492 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2492 2786 4
  · have he : independentCachedBranchMembers2492.erase 2786=independentCachedBranchMembers2490 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2490
  · have he : independentCachedBranchMembers2492.filter (independentCachedEdge 2786)=independentCachedBranchMembers2491 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2491
def independentCachedBranchMembers2493 : Finset ℕ := ([1644,1692,1720,1764,2620,2740,2764,2792,3126,3178,3226,3270] : List ℕ).toFinset
theorem independentCachedBranchBound2493 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2493 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2493 4 (fun x => (if x<2764 then (if x<1764 then (if x<1692 then 0 else (if x<1720 then 0 else 1)) else (if x<2620 then 1 else (if x<2740 then 0 else 1))) else (if x<3178 then (if x<2792 then 0 else (if x<3126 then 1 else 2)) else (if x<3226 then 2 else (if x<3270 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2494 : Finset ℕ := ([48,72,1594,1644,1686,1692,1714,1720,1738,1764,2614,2620,2638,2714,2740,2764,2786,2792,3126,3132,3178,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2494 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2494 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2494 2614 4
  · have he : independentCachedBranchMembers2494.erase 2614=independentCachedBranchMembers2492 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2492
  · have he : independentCachedBranchMembers2494.filter (independentCachedEdge 2614)=independentCachedBranchMembers2493 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2493
def independentCachedBranchMembers2495 : Finset ℕ := ([72,1644,1686,1692,1714,1720,2638,2714,2740,3178,3226,3252] : List ℕ).toFinset
theorem independentCachedBranchBound2495 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2495 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2495 4 (fun x => (if x<2638 then (if x<1692 then (if x<1644 then 0 else (if x<1686 then 0 else 1)) else (if x<1714 then 2 else (if x<1720 then 2 else 1))) else (if x<3178 then (if x<2714 then 0 else (if x<2740 then 1 else 1)) else (if x<3226 then 0 else (if x<3252 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2496 : Finset ℕ := ([48,72,192,1594,1644,1686,1692,1714,1720,1738,1764,2614,2620,2638,2714,2740,2764,2786,2792,3126,3132,3178,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2496 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2496 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2496 192 4
  · have he : independentCachedBranchMembers2496.erase 192=independentCachedBranchMembers2494 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2494
  · have he : independentCachedBranchMembers2496.filter (independentCachedEdge 192)=independentCachedBranchMembers2495 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2495
def independentCachedBranchMembers2497 : Finset ℕ := ([72,1644,1692,1714,2620,2638,2764,2786,3126,3178,3226,3252,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2497 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2497 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2497 4 (fun x => (if x<2786 then (if x<1714 then (if x<1644 then 0 else (if x<1692 then 0 else 1)) else (if x<2638 then (if x<2620 then 1 else 2) else (if x<2764 then 0 else 1))) else (if x<3226 then (if x<3126 then 1 else (if x<3178 then 2 else 0)) else (if x<3270 then (if x<3252 then 3 else 3) else (if x<3304 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2498 : Finset ℕ := ([48,72,192,1594,1644,1686,1692,1714,1720,1738,1764,2614,2620,2638,2714,2740,2758,2764,2786,2792,3126,3132,3178,3226,3252,3270,3276,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2498 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2498 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2498 2758 4
  · have he : independentCachedBranchMembers2498.erase 2758=independentCachedBranchMembers2496 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2496
  · have he : independentCachedBranchMembers2498.filter (independentCachedEdge 2758)=independentCachedBranchMembers2497 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2497
def independentCachedBranchMembers2499 : Finset ℕ := ([72,1594,1644,1686,1720,2614,2638,2714,2740,2764,2786,3132,3178,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2499 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2499 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2499 4 (fun x => (if x<2714 then (if x<1686 then (if x<1594 then 0 else (if x<1644 then 1 else 0)) else (if x<2614 then (if x<1720 then 1 else 2) else (if x<2638 then 1 else 0))) else (if x<3132 then (if x<2764 then (if x<2740 then 1 else 2) else (if x<2786 then 3 else 3)) else (if x<3270 then (if x<3178 then 2 else 0) else (if x<3304 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2500 : Finset ℕ := ([1644,1686,2714,2786,3178,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2500 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2500 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2500 3 (fun x => (if x<2786 then (if x<1686 then 0 else (if x<2714 then 1 else 0)) else (if x<3178 then 2 else (if x<3304 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2501 : Finset ℕ := ([48,72,1594,1644,1686,1720,2614,2638,2714,2740,2764,2786,3132,3178,3270,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2501 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2501 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2501 48 3
  · have he : independentCachedBranchMembers2501.erase 48=independentCachedBranchMembers2499 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2499
  · have he : independentCachedBranchMembers2501.filter (independentCachedEdge 48)=independentCachedBranchMembers2500 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2500
def independentCachedBranchMembers2502 : Finset ℕ := ([48,72,192,1594,1644,1686,1692,1714,1720,1738,1764,2614,2620,2638,2714,2740,2758,2764,2786,2792,3126,3132,3178,3226,3252,3270,3276,3298,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2502 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2502 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2502 3298 4
  · have he : independentCachedBranchMembers2502.erase 3298=independentCachedBranchMembers2498 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2498
  · have he : independentCachedBranchMembers2502.filter (independentCachedEdge 3298)=independentCachedBranchMembers2501 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2501
def independentCachedBranchMembers2503 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1690,1692,1714,1720,1734,1738,1740,1762,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2716,2738,2740,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3178,3180,3222,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2503 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2503 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2503 1690 5
  · have he : independentCachedBranchMembers2503.erase 1690=independentCachedBranchMembers2489 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2489
  · have he : independentCachedBranchMembers2503.filter (independentCachedEdge 1690)=independentCachedBranchMembers2502 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2502
def independentCachedBranchMembers2504 : Finset ℕ := ([18,192,1590,1594,1596,1614,1686,1690,1762,1764,1768,2614,2618,2620,2638,2710,2716,2788,2792,3102,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2504 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2504 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2504 5 (fun x => (if x<2638 then (if x<1690 then (if x<1594 then (if x<192 then 0 else (if x<1590 then 0 else 0)) else (if x<1614 then (if x<1596 then 1 else 2) else (if x<1686 then 1 else 1))) else (if x<1768 then (if x<1762 then 2 else (if x<1764 then 1 else 0)) else (if x<2618 then (if x<2614 then 2 else 3) else (if x<2620 then 0 else 4)))) else (if x<3180 then (if x<2788 then (if x<2710 then 3 else (if x<2716 then 4 else 3)) else (if x<3102 then (if x<2792 then 3 else 0) else (if x<3178 then 0 else 1))) else (if x<3256 then (if x<3250 then 2 else (if x<3252 then 1 else 3)) else (if x<3274 then (if x<3270 then 2 else 1) else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2505 : Finset ℕ := ([18,1590,1594,1614,1686,1690,1762,2620,2716,2788,2792,3180,3252,3256,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2505 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2505 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2505 4 (fun x => (if x<2620 then (if x<1614 then (if x<1590 then 0 else (if x<1594 then 0 else 1)) else (if x<1690 then (if x<1686 then 1 else 1) else (if x<1762 then 0 else 1))) else (if x<3180 then (if x<2788 then (if x<2716 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3256 then (if x<3252 then 2 else 2) else (if x<3276 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2506 : Finset ℕ := ([18,192,1590,1594,1596,1614,1686,1690,1762,1764,1768,2614,2618,2620,2638,2710,2716,2786,2788,2792,3102,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2506 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2506 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2506 2786 4
  · have he : independentCachedBranchMembers2506.erase 2786=independentCachedBranchMembers2504 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2504
  · have he : independentCachedBranchMembers2506.filter (independentCachedEdge 2786)=independentCachedBranchMembers2505 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2505
def independentCachedBranchMembers2507 : Finset ℕ := ([192,1590,1596,1614,1690,1762,1768,2618,2710,2716,2788,3178,3252,3270,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2507 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2507 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2507 4 (fun x => (if x<2618 then (if x<1614 then (if x<1590 then 0 else (if x<1596 then 0 else 1)) else (if x<1762 then (if x<1690 then 1 else 1) else (if x<1768 then 0 else 1))) else (if x<3178 then (if x<2716 then (if x<2710 then 2 else 2) else (if x<2788 then 3 else 3)) else (if x<3270 then (if x<3252 then 2 else 3) else (if x<3276 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2508 : Finset ℕ := ([18,192,1590,1594,1596,1614,1686,1690,1762,1764,1768,2614,2618,2620,2638,2710,2714,2716,2786,2788,2792,3102,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2508 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2508 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2508 2714 4
  · have he : independentCachedBranchMembers2508.erase 2714=independentCachedBranchMembers2506 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2506
  · have he : independentCachedBranchMembers2508.filter (independentCachedEdge 2714)=independentCachedBranchMembers2507 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2507
def independentCachedBranchMembers2509 : Finset ℕ := ([192,1596,1686,1690,1762,2614,2618,2638,2716,2788,2792,3180,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2509 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2509 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2509 4 (fun x => (if x<2638 then (if x<1690 then (if x<1596 then 0 else (if x<1686 then 0 else 1)) else (if x<2614 then (if x<1762 then 2 else 1) else (if x<2618 then 0 else 2))) else (if x<3180 then (if x<2788 then (if x<2716 then 3 else 1) else (if x<2792 then 3 else 1)) else (if x<3270 then (if x<3250 then 3 else 2) else (if x<3274 then 3 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2510 : Finset ℕ := ([1596,1762,2638,2716,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2510 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2510 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2510 3 (fun x => (if x<2716 then (if x<1762 then 0 else (if x<2638 then 1 else 2)) else (if x<3270 then 0 else (if x<3274 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2511 : Finset ℕ := ([18,192,1596,1686,1690,1762,2614,2618,2638,2716,2788,2792,3180,3250,3270,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2511 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2511 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2511 18 3
  · have he : independentCachedBranchMembers2511.erase 18=independentCachedBranchMembers2509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2509
  · have he : independentCachedBranchMembers2511.filter (independentCachedEdge 18)=independentCachedBranchMembers2510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2510
def independentCachedBranchMembers2512 : Finset ℕ := ([18,192,1590,1594,1596,1614,1686,1690,1692,1762,1764,1768,2614,2618,2620,2638,2710,2714,2716,2786,2788,2792,3102,3178,3180,3250,3252,3256,3270,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2512 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2512 1692 4
  · have he : independentCachedBranchMembers2512.erase 1692=independentCachedBranchMembers2508 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2508
  · have he : independentCachedBranchMembers2512.filter (independentCachedEdge 1692)=independentCachedBranchMembers2511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2511
def independentCachedBranchMembers2513 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1690,1692,1714,1720,1734,1738,1740,1762,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2716,2738,2740,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3150,3178,3180,3222,3226,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2513 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2513 3150 5
  · have he : independentCachedBranchMembers2513.erase 3150=independentCachedBranchMembers2503 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2503
  · have he : independentCachedBranchMembers2513.filter (independentCachedEdge 3150)=independentCachedBranchMembers2512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2512
def independentCachedBranchMembers2514 : Finset ℕ := ([18,48,72,192,1590,1594,1644,1692,1714,1734,1738,1768,2614,2618,2638,2716,2738,2758,2762,2788,2792,3102,3132,3178,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2514 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2514 5 (fun x => (if x<2716 then (if x<1692 then (if x<192 then (if x<48 then 0 else (if x<72 then 1 else 0)) else (if x<1594 then (if x<1590 then 1 else 0) else (if x<1644 then 1 else 0))) else (if x<1768 then (if x<1734 then (if x<1714 then 2 else 2) else (if x<1738 then 2 else 1)) else (if x<2618 then (if x<2614 then 2 else 1) else (if x<2638 then 3 else 3)))) else (if x<3132 then (if x<2762 then (if x<2738 then 3 else (if x<2758 then 0 else 1)) else (if x<2792 then (if x<2788 then 4 else 4) else (if x<3102 then 0 else 3))) else (if x<3252 then (if x<3222 then (if x<3178 then 1 else 3) else (if x<3226 then 0 else 4)) else (if x<3276 then (if x<3256 then 4 else 2) else (if x<3298 then 0 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2515 : Finset ℕ := ([48,192,1590,1594,1644,1692,1734,1738,2638,2738,2788,2792,3102,3252,3256,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2515 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2515 4 (fun x => (if x<2638 then (if x<1644 then (if x<1590 then (if x<192 then 0 else 0) else (if x<1594 then 0 else 1)) else (if x<1734 then (if x<1692 then 1 else 1) else (if x<1738 then 0 else 1))) else (if x<3102 then (if x<2788 then (if x<2738 then 2 else 3) else (if x<2792 then 2 else 3)) else (if x<3256 then (if x<3252 then 2 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2516 : Finset ℕ := ([18,48,72,192,1590,1594,1644,1692,1714,1734,1738,1768,2614,2618,2638,2668,2716,2738,2758,2762,2788,2792,3102,3132,3178,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2516 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2516 2668 4
  · have he : independentCachedBranchMembers2516.erase 2668=independentCachedBranchMembers2514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2514
  · have he : independentCachedBranchMembers2516.filter (independentCachedEdge 2668)=independentCachedBranchMembers2515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2515
def independentCachedBranchMembers2517 : Finset ℕ := ([72,1594,1644,1734,1768,2614,2638,2716,2738,2762,2788,3132,3178,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2517 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2517 4 (fun x => (if x<2716 then (if x<1734 then (if x<1594 then 0 else (if x<1644 then 1 else 0)) else (if x<2614 then (if x<1768 then 2 else 1) else (if x<2638 then 1 else 0))) else (if x<3132 then (if x<2762 then (if x<2738 then 3 else 3) else (if x<2788 then 2 else 1)) else (if x<3222 then (if x<3178 then 2 else 0) else (if x<3256 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2518 : Finset ℕ := ([1644,1768,2716,2788,3178,3222] : List ℕ).toFinset
theorem independentCachedBranchBound2518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2518 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2518 3 (fun x => (if x<2788 then (if x<1768 then 0 else (if x<2716 then 1 else 2)) else (if x<3178 then 0 else (if x<3222 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2519 : Finset ℕ := ([48,72,1594,1644,1734,1768,2614,2638,2716,2738,2762,2788,3132,3178,3222,3256] : List ℕ).toFinset
theorem independentCachedBranchBound2519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2519 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2519 48 3
  · have he : independentCachedBranchMembers2519.erase 48=independentCachedBranchMembers2517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2517
  · have he : independentCachedBranchMembers2519.filter (independentCachedEdge 48)=independentCachedBranchMembers2518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2518
def independentCachedBranchMembers2520 : Finset ℕ := ([18,48,72,192,1590,1594,1644,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2716,2738,2758,2762,2788,2792,3102,3132,3178,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2520 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2520 1764 4
  · have he : independentCachedBranchMembers2520.erase 1764=independentCachedBranchMembers2516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2516
  · have he : independentCachedBranchMembers2520.filter (independentCachedEdge 1764)=independentCachedBranchMembers2519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2519
def independentCachedBranchMembers2521 : Finset ℕ := ([192,1644,1714,1734,1738,2614,2618,2638,2716,2788,2792,3132,3222,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2521 4 (fun x => (if x<2638 then (if x<1734 then (if x<1644 then 0 else (if x<1714 then 1 else 2)) else (if x<2614 then (if x<1738 then 0 else 1) else (if x<2618 then 2 else 0))) else (if x<3132 then (if x<2788 then (if x<2716 then 1 else 3) else (if x<2792 then 3 else 1)) else (if x<3226 then (if x<3222 then 0 else 2) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2522 : Finset ℕ := ([1734,1738,2638,2716,3132,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2522 3 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2522 3 (fun x => (if x<2716 then (if x<1738 then 0 else (if x<2638 then 1 else 0)) else (if x<3132 then 2 else (if x<3298 then 1 else 2))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2523 : Finset ℕ := ([18,192,1644,1714,1734,1738,2614,2618,2638,2716,2788,2792,3132,3222,3226,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2523 4 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2523 18 3
  · have he : independentCachedBranchMembers2523.erase 18=independentCachedBranchMembers2521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2521
  · have he : independentCachedBranchMembers2523.filter (independentCachedEdge 18)=independentCachedBranchMembers2522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2522
def independentCachedBranchMembers2524 : Finset ℕ := ([18,48,72,192,1590,1594,1614,1644,1692,1714,1734,1738,1764,1768,2614,2618,2638,2668,2716,2738,2758,2762,2788,2792,3102,3132,3178,3222,3226,3252,3256,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound2524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2524 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2524 1614 4
  · have he : independentCachedBranchMembers2524.erase 1614=independentCachedBranchMembers2520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2520
  · have he : independentCachedBranchMembers2524.filter (independentCachedEdge 1614)=independentCachedBranchMembers2523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2523
def independentCachedBranchMembers2525 : Finset ℕ := ([18,48,72,192,1590,1594,1596,1614,1642,1644,1686,1690,1692,1714,1720,1734,1738,1740,1762,1764,1768,2614,2618,2620,2638,2662,2668,2710,2714,2716,2738,2740,2758,2762,2764,2786,2788,2792,3102,3126,3130,3132,3150,3178,3180,3222,3226,3228,3250,3252,3256,3270,3274,3276,3298,3300,3304] : List ℕ).toFinset
theorem independentCachedBranchBound2525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2525 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2525 3228 5
  · have he : independentCachedBranchMembers2525.erase 3228=independentCachedBranchMembers2513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2513
  · have he : independentCachedBranchMembers2525.filter (independentCachedEdge 3228)=independentCachedBranchMembers2524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2524
def independentCachedBranchMembers2526 : Finset ℕ := ([12,18,48,72,80,130,132,192,222,250,252,1582,1590,1594,1596,1614,1622,1626,1628,1642,1644,1650,1652,1678,1686,1690,1692,1702,1708,1714,1720,1734,1738,1740,1746,1748,1752,1762,1764,1768,1776,2606,2614,2618,2620,2638,2646,2650,2652,2662,2668,2674,2680,2702,2710,2714,2716,2730,2732,2738,2740,2758,2762,2764,2770,2772,2776,2786,2788,2792,2800,3102,3118,3126,3130,3132,3150,3158,3162,3164,3178,3180,3186,3188,3192,3214,3222,3226,3228,3238,3242,3244,3250,3252,3256,3270,3274,3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2526 7 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2526 80 6
  · have he : independentCachedBranchMembers2526.erase 80=independentCachedBranchMembers2400 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2400
  · have he : independentCachedBranchMembers2526.filter (independentCachedEdge 80)=independentCachedBranchMembers2525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2525
def independentCachedBranchMembers2527 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1776,2638,2652,2674,2702,2714,2740,2764,2776,2786,3102,3150,3188,3228,3238,3250,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2527 6 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2527 6 (fun x => (if x<2702 then (if x<1678 then (if x<222 then (if x<48 then 0 else (if x<72 then 0 else 1)) else (if x<1626 then (if x<1590 then 1 else 2) else (if x<1628 then 1 else 2))) else (if x<1776 then (if x<1714 then (if x<1692 then 0 else 3) else (if x<1738 then 0 else 3)) else (if x<2652 then (if x<2638 then 2 else 0) else (if x<2674 then 1 else 0)))) else (if x<3150 then (if x<2764 then (if x<2714 then 3 else (if x<2740 then 4 else 3)) else (if x<2786 then (if x<2776 then 4 else 2) else (if x<3102 then 3 else 5))) else (if x<3250 then (if x<3228 then (if x<3188 then 1 else 5) else (if x<3238 then 4 else 5)) else (if x<3276 then (if x<3274 then 4 else 4) else (if x<3288 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2528 : Finset ℕ := ([72,222,1628,1738,2638,2652,2674,2714,2740,2776,3188,3228,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2528 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2528 5 (fun x => (if x<2714 then (if x<1738 then (if x<222 then 0 else (if x<1628 then 0 else 0)) else (if x<2652 then (if x<2638 then 0 else 0) else (if x<2674 then 1 else 1))) else (if x<3188 then (if x<2740 then 1 else (if x<2776 then 1 else 0)) else (if x<3250 then (if x<3228 then 1 else 1) else (if x<3276 then 1 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2529 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1776,2638,2652,2674,2702,2714,2740,2764,2776,2786,3102,3150,3186,3188,3228,3238,3250,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2529 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2529 3186 5
  · have he : independentCachedBranchMembers2529.erase 3186=independentCachedBranchMembers2527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2527
  · have he : independentCachedBranchMembers2529.filter (independentCachedEdge 3186)=independentCachedBranchMembers2528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2528
def independentCachedBranchMembers2530 : Finset ℕ := ([12,222,1590,1626,1628,1678,1692,1776,2674,2740,2764,2776,3150,3228] : List ℕ).toFinset
theorem independentCachedBranchBound2530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2530 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2530 5 (fun x => (if x<1776 then (if x<1626 then (if x<222 then 0 else (if x<1590 then 0 else 1)) else (if x<1678 then (if x<1628 then 1 else 0) else (if x<1692 then 0 else 1))) else (if x<2764 then (if x<2674 then 1 else (if x<2740 then 1 else 1)) else (if x<3150 then (if x<2776 then 0 else 1) else (if x<3228 then 0 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2531 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1776,2614,2638,2652,2674,2702,2714,2740,2764,2776,2786,3102,3150,3186,3188,3228,3238,3250,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2531 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2531 2614 5
  · have he : independentCachedBranchMembers2531.erase 2614=independentCachedBranchMembers2529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2529
  · have he : independentCachedBranchMembers2531.filter (independentCachedEdge 2614)=independentCachedBranchMembers2530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2530
def independentCachedBranchMembers2532 : Finset ℕ := ([1590,1628,1678,1692,1714,1738,2714,2740,2764,2786,3102,3188,3238,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2532 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2532 5 (fun x => (if x<2740 then (if x<1692 then (if x<1628 then 0 else (if x<1678 then 0 else 0)) else (if x<1738 then (if x<1714 then 1 else 1) else (if x<2714 then 1 else 1))) else (if x<3102 then (if x<2764 then 1 else (if x<2786 then 0 else 1)) else (if x<3238 then (if x<3188 then 2 else 2) else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2533 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1740,1776,2614,2638,2652,2674,2702,2714,2740,2764,2776,2786,3102,3150,3186,3188,3228,3238,3250,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2533 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2533 1740 5
  · have he : independentCachedBranchMembers2533.erase 1740=independentCachedBranchMembers2531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2531
  · have he : independentCachedBranchMembers2533.filter (independentCachedEdge 1740)=independentCachedBranchMembers2532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2532
def independentCachedBranchMembers2534 : Finset ℕ := ([12,222,1628,1678,1740,2652,2674,2702,2714,2740,2764,2776,2786,3150,3188,3228,3238,3250,3274] : List ℕ).toFinset
theorem independentCachedBranchBound2534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2534 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2534 5 (fun x => (if x<2740 then (if x<1740 then (if x<1628 then (if x<222 then 0 else 0) else (if x<1678 then 0 else 0)) else (if x<2674 then (if x<2652 then 1 else 1) else (if x<2702 then 1 else (if x<2714 then 2 else 3)))) else (if x<3188 then (if x<2776 then (if x<2764 then 2 else 0) else (if x<2786 then 2 else (if x<3150 then 2 else 0))) else (if x<3238 then (if x<3228 then 3 else 0) else (if x<3250 then 2 else (if x<3274 then 1 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2535 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1740,1776,2614,2638,2652,2674,2702,2714,2740,2764,2776,2786,3102,3150,3186,3188,3228,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2535 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2535 3252 5
  · have he : independentCachedBranchMembers2535.erase 3252=independentCachedBranchMembers2533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2533
  · have he : independentCachedBranchMembers2535.filter (independentCachedEdge 3252)=independentCachedBranchMembers2534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2534
def independentCachedBranchMembers2536 : Finset ℕ := ([72,222,1590,1626,1628,1692,1738,1740,1776,2638,2674,2702,2740,2776,2786,3228,3238,3274,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2536 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2536 5 (fun x => (if x<2638 then (if x<1628 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1626 then 1 else 0)) else (if x<1738 then (if x<1692 then 1 else 2) else (if x<1740 then 2 else (if x<1776 then 0 else 1)))) else (if x<2786 then (if x<2702 then (if x<2674 then 0 else 3) else (if x<2740 then 2 else (if x<2776 then 2 else 0))) else (if x<3238 then (if x<3228 then 2 else 3) else (if x<3274 then 4 else (if x<3276 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2537 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1740,1776,2614,2638,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3186,3188,3228,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2537 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2537 2800 5
  · have he : independentCachedBranchMembers2537.erase 2800=independentCachedBranchMembers2535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2535
  · have he : independentCachedBranchMembers2537.filter (independentCachedEdge 2800)=independentCachedBranchMembers2536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2536
def independentCachedBranchMembers2538 : Finset ℕ := ([12,48,1590,1626,1678,1692,1714,1740,1776,2638,2652,2674,2714,2740,2776,3188,3228,3250,3276] : List ℕ).toFinset
theorem independentCachedBranchBound2538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2538 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2538 5 (fun x => (if x<2638 then (if x<1678 then (if x<1590 then (if x<48 then 0 else 0) else (if x<1626 then 1 else 1)) else (if x<1714 then (if x<1692 then 0 else 1) else (if x<1740 then 0 else (if x<1776 then 2 else 1)))) else (if x<2776 then (if x<2674 then (if x<2652 then 0 else 2) else (if x<2714 then 0 else (if x<2740 then 3 else 1))) else (if x<3228 then (if x<3188 then 1 else 3) else (if x<3250 then 2 else (if x<3276 then 2 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2539 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1740,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3186,3188,3228,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2539 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2539 2650 5
  · have he : independentCachedBranchMembers2539.erase 2650=independentCachedBranchMembers2537 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2537
  · have he : independentCachedBranchMembers2539.filter (independentCachedEdge 2650)=independentCachedBranchMembers2538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2538
def independentCachedBranchMembers2540 : Finset ℕ := ([12,48,72,222,1626,1740,1776,2614,2638,2652,2674,2702,2776,3150,3186,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2540 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2540 5 (fun x => (if x<2652 then (if x<1626 then (if x<72 then (if x<48 then 0 else 0) else (if x<222 then 1 else 1)) else (if x<1776 then (if x<1740 then 1 else 0) else (if x<2614 then 0 else (if x<2638 then 2 else 0)))) else (if x<3186 then (if x<2702 then (if x<2674 then 1 else 0) else (if x<2776 then 2 else (if x<3150 then 3 else 1))) else (if x<3250 then (if x<3228 then 2 else 3) else (if x<3274 then 0 else (if x<3288 then 2 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2541 : Finset ℕ := ([12,48,72,222,1590,1626,1628,1678,1692,1714,1738,1740,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3186,3188,3228,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2541 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2541 1764 5
  · have he : independentCachedBranchMembers2541.erase 1764=independentCachedBranchMembers2539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2539
  · have he : independentCachedBranchMembers2541.filter (independentCachedEdge 1764)=independentCachedBranchMembers2540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2540
def independentCachedBranchMembers2542 : Finset ℕ := ([1626,1628,1678,1714,1738,1740,1776,2614,2638,2674,2714,2776,2786,3150,3186,3188,3228,3238,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2542 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2542 5 (fun x => (if x<2674 then (if x<1738 then (if x<1678 then (if x<1628 then 0 else 1) else (if x<1714 then 0 else 0)) else (if x<1776 then (if x<1740 then 1 else 2) else (if x<2614 then 1 else (if x<2638 then 2 else 0)))) else (if x<3186 then (if x<2776 then (if x<2714 then 0 else 0) else (if x<2786 then 1 else (if x<3150 then 1 else 3))) else (if x<3228 then (if x<3188 then 2 else 3) else (if x<3238 then 3 else (if x<3288 then 3 else 2))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2543 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1678,1692,1714,1738,1740,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3186,3188,3228,3238,3250,3252,3274,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2543 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2543 1614 5
  · have he : independentCachedBranchMembers2543.erase 1614=independentCachedBranchMembers2541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2541
  · have he : independentCachedBranchMembers2543.filter (independentCachedEdge 1614)=independentCachedBranchMembers2542 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2542
def independentCachedBranchMembers2544 : Finset ℕ := ([72,222,1590,1626,1628,1692,1738,1740,1776,2614,2650,2652,2714,2764,2800,3102,3150,3186,3188,3250,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2544 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2544 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2544 5 (fun x => (if x<2652 then (if x<1692 then (if x<1590 then (if x<222 then 0 else 0) else (if x<1626 then 1 else (if x<1628 then 0 else 1))) else (if x<1776 then (if x<1738 then 2 else (if x<1740 then 2 else 0)) else (if x<2614 then 1 else (if x<2650 then 3 else 3)))) else (if x<3150 then (if x<2764 then (if x<2714 then 0 else 2) else (if x<2800 then 2 else (if x<3102 then 3 else 1))) else (if x<3250 then (if x<3186 then 0 else (if x<3188 then 3 else 1)) else (if x<3252 then 1 else (if x<3288 then 3 else 0))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2545 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1678,1692,1714,1738,1740,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3186,3188,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2545 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2545 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2545 3312 5
  · have he : independentCachedBranchMembers2545.erase 3312=independentCachedBranchMembers2543 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2543
  · have he : independentCachedBranchMembers2545.filter (independentCachedEdge 3312)=independentCachedBranchMembers2544 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2544
def independentCachedBranchMembers2546 : Finset ℕ := ([48,1590,1628,1678,1738,1764,1776,2614,2652,2674,2702,2714,2740,2800,3102,3150,3188,3228,3238,3250,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2546 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2546 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2546 5 (fun x => (if x<2714 then (if x<1764 then (if x<1628 then (if x<1590 then 0 else 0) else (if x<1678 then 1 else (if x<1738 then 0 else 1))) else (if x<2652 then (if x<1776 then 1 else (if x<2614 then 2 else 3)) else (if x<2674 then 3 else (if x<2702 then 0 else 2)))) else (if x<3188 then (if x<2800 then (if x<2740 then 3 else 2) else (if x<3102 then 3 else (if x<3150 then 3 else 2))) else (if x<3250 then (if x<3228 then 0 else (if x<3238 then 4 else 4)) else (if x<3276 then 3 else (if x<3288 then 0 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2547 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1678,1692,1714,1738,1740,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3164,3186,3188,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2547 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2547 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2547 3164 5
  · have he : independentCachedBranchMembers2547.erase 3164=independentCachedBranchMembers2545 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2545
  · have he : independentCachedBranchMembers2547.filter (independentCachedEdge 3164)=independentCachedBranchMembers2546 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2546
def independentCachedBranchMembers2548 : Finset ℕ := ([12,48,1590,1626,1628,1692,1738,1740,1776,2638,2674,2702,2740,2776,2786,3102,3150,3186,3188,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2548 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2548 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2548 5 (fun x => (if x<2674 then (if x<1692 then (if x<1590 then (if x<48 then 0 else 0) else (if x<1626 then 1 else (if x<1628 then 1 else 2))) else (if x<1740 then (if x<1738 then 1 else 2) else (if x<1776 then 0 else (if x<2638 then 0 else 0)))) else (if x<3102 then (if x<2740 then (if x<2702 then 0 else 3) else (if x<2776 then 1 else (if x<2786 then 1 else 2))) else (if x<3188 then (if x<3150 then 3 else (if x<3186 then 4 else 3)) else (if x<3250 then 4 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2549 : Finset ℕ := ([12,1628,1740,2674,2702,2740,2776,2786,3150,3188,3250] : List ℕ).toFinset
theorem independentCachedBranchBound2549 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2549 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2549 4 (fun x => (if x<2740 then (if x<1740 then (if x<1628 then 0 else 0) else (if x<2674 then 1 else (if x<2702 then 1 else 2))) else (if x<3150 then (if x<2776 then 2 else (if x<2786 then 1 else 0)) else (if x<3188 then 2 else (if x<3250 then 2 else 0)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2550 : Finset ℕ := ([12,48,1590,1626,1628,1692,1738,1740,1776,2638,2674,2702,2740,2776,2786,3102,3150,3186,3188,3250,3252,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2550 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2550 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2550 3252 4
  · have he : independentCachedBranchMembers2550.erase 3252=independentCachedBranchMembers2548 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2548
  · have he : independentCachedBranchMembers2550.filter (independentCachedEdge 3252)=independentCachedBranchMembers2549 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2549
def independentCachedBranchMembers2551 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1678,1692,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3164,3186,3188,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2551 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2551 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2551 1752 5
  · have he : independentCachedBranchMembers2551.erase 1752=independentCachedBranchMembers2547 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2547
  · have he : independentCachedBranchMembers2551.filter (independentCachedEdge 1752)=independentCachedBranchMembers2550 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2550
def independentCachedBranchMembers2552 : Finset ℕ := ([12,72,222,1590,1628,1678,1738,1764,1776,2638,2650,2764,2776,2786,3102,3150,3188,3228,3238,3250,3276,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2552 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2552 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2552 5 (fun x => (if x<2764 then (if x<1678 then (if x<222 then (if x<72 then 0 else 1) else (if x<1590 then 0 else (if x<1628 then 1 else 0))) else (if x<1776 then (if x<1738 then 0 else (if x<1764 then 2 else 2)) else (if x<2638 then 3 else (if x<2650 then 0 else 2)))) else (if x<3188 then (if x<2786 then (if x<2776 then 1 else 3) else (if x<3102 then 2 else (if x<3150 then 0 else 4))) else (if x<3250 then (if x<3228 then 4 else (if x<3238 then 4 else 4)) else (if x<3276 then 1 else (if x<3288 then 0 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2553 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1652,1678,1692,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3164,3186,3188,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2553 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2553 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2553 1652 5
  · have he : independentCachedBranchMembers2553.erase 1652=independentCachedBranchMembers2551 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2551
  · have he : independentCachedBranchMembers2553.filter (independentCachedEdge 1652)=independentCachedBranchMembers2552 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2552
def independentCachedBranchMembers2554 : Finset ℕ := ([12,48,72,1590,1614,1628,1740,1776,2614,2638,2652,2674,2714,2740,2764,2786,2800,3102,3188,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2554 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2554 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2554 5 (fun x => (if x<2674 then (if x<1628 then (if x<72 then (if x<48 then 0 else 0) else (if x<1590 then 1 else (if x<1614 then 1 else 0))) else (if x<2614 then (if x<1740 then 1 else (if x<1776 then 2 else 2)) else (if x<2638 then 3 else (if x<2652 then 2 else 3)))) else (if x<3102 then (if x<2764 then (if x<2714 then 2 else (if x<2740 then 3 else 4)) else (if x<2786 then 0 else (if x<2800 then 4 else 0))) else (if x<3250 then (if x<3188 then 3 else (if x<3228 then 3 else 4)) else (if x<3274 then 0 else (if x<3288 then 4 else 1))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2555 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1652,1678,1692,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2764,2776,2786,2800,3102,3150,3164,3186,3188,3226,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2555 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2555 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2555 3226 5
  · have he : independentCachedBranchMembers2555.erase 3226=independentCachedBranchMembers2553 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2553
  · have he : independentCachedBranchMembers2555.filter (independentCachedEdge 3226)=independentCachedBranchMembers2554 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2554
def independentCachedBranchMembers2556 : Finset ℕ := ([12,1628,1692,1714,1738,1764,1776,2614,2638,2650,2702,2714,2740,2764,2776,2786,3102,3164,3186,3228,3238,3250,3274,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2556 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2556 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2556 5 (fun x => (if x<2740 then (if x<1776 then (if x<1714 then (if x<1628 then 0 else (if x<1692 then 0 else 1)) else (if x<1738 then 1 else (if x<1764 then 1 else 1))) else (if x<2650 then (if x<2614 then 0 else (if x<2638 then 2 else 0)) else (if x<2702 then 2 else (if x<2714 then 2 else 1)))) else (if x<3186 then (if x<2786 then (if x<2764 then 1 else (if x<2776 then 1 else 3)) else (if x<3102 then 0 else (if x<3164 then 0 else 3))) else (if x<3250 then (if x<3228 then 2 else (if x<3238 then 4 else 2)) else (if x<3274 then 0 else (if x<3312 then 2 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2557 : Finset ℕ := ([12,48,72,222,1590,1614,1626,1628,1652,1678,1692,1714,1738,1740,1752,1764,1776,2614,2638,2650,2652,2674,2702,2714,2740,2762,2764,2776,2786,2800,3102,3150,3164,3186,3188,3226,3228,3238,3250,3252,3274,3276,3288,3312] : List ℕ).toFinset
theorem independentCachedBranchBound2557 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2557 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers2557 2762 5
  · have he : independentCachedBranchMembers2557.erase 2762=independentCachedBranchMembers2555 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2555
  · have he : independentCachedBranchMembers2557.filter (independentCachedEdge 2762)=independentCachedBranchMembers2556 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound2556
def independentCachedBranchMembers2558 : Finset ℕ := ([222,1626,1678,1692,1714,1738,1752,1764,2614,2638,2652,2674,2714,2740,2764,2786,2800,3102,3188,3228,3250,3274,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2558 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2558 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2558 5 (fun x => (if x<2674 then (if x<1738 then (if x<1678 then (if x<1626 then 0 else 0) else (if x<1692 then 0 else (if x<1714 then 1 else 1))) else (if x<2614 then (if x<1752 then 1 else (if x<1764 then 2 else 1)) else (if x<2638 then 2 else (if x<2652 then 0 else 2)))) else (if x<3102 then (if x<2764 then (if x<2714 then 3 else (if x<2740 then 0 else 1)) else (if x<2786 then 1 else (if x<2800 then 1 else 2))) else (if x<3250 then (if x<3188 then 0 else (if x<3228 then 3 else 3)) else (if x<3274 then 3 else (if x<3288 then 0 else 4))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers2559 : Finset ℕ := ([222,1678,1738,1764,2638,2764,2786,3102,3188,3228,3250,3288] : List ℕ).toFinset
theorem independentCachedBranchBound2559 : ListCliqueBound independentCachedEdge independentCachedBranchMembers2559 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers2559 4 (fun x => (if x<2786 then (if x<1764 then (if x<1678 then 0 else (if x<1738 then 0 else 1)) else (if x<2638 then 1 else (if x<2764 then 0 else 1))) else (if x<3228 then (if x<3102 then 1 else (if x<3188 then 0 else 2)) else (if x<3250 then 2 else (if x<3288 then 2 else 3)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
