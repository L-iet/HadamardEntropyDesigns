/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCachedBranch53
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentCachedBranchMembers4512 : Finset ℕ := ([1590,1626,1644,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2714,2732,2738,2792,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4512 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4512 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4512 1702 4
  · have he : independentCachedBranchMembers4512.erase 1702=independentCachedBranchMembers4510 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4510
  · have he : independentCachedBranchMembers4512.filter (independentCachedEdge 1702)=independentCachedBranchMembers4511 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4511
def independentCachedBranchMembers4513 : Finset ℕ := ([1590,1626,1720,1748,2620,2680,2714,2738,3164,3188,3222,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4513 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4513 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4513 4 (fun x => (if x<2714 then (if x<1748 then (if x<1626 then 0 else (if x<1720 then 0 else 0)) else (if x<2620 then 0 else (if x<2680 then 1 else 2))) else (if x<3188 then (if x<2738 then 1 else (if x<3164 then 2 else 2)) else (if x<3222 then 1 else (if x<3282 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4514 : Finset ℕ := ([238,1590,1626,1644,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2714,2732,2738,2792,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4514 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4514 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4514 238 4
  · have he : independentCachedBranchMembers4514.erase 238=independentCachedBranchMembers4512 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4512
  · have he : independentCachedBranchMembers4514.filter (independentCachedEdge 238)=independentCachedBranchMembers4513 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4513
def independentCachedBranchMembers4515 : Finset ℕ := ([1590,1626,1720,1748,2638,2662,2732,2792,3118,3178,3276,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4515 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4515 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4515 4 (fun x => (if x<2732 then (if x<1748 then (if x<1626 then 0 else (if x<1720 then 0 else 0)) else (if x<2638 then 0 else (if x<2662 then 1 else 2))) else (if x<3178 then (if x<2792 then 1 else (if x<3118 then 2 else 1)) else (if x<3276 then 2 else (if x<3300 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4516 : Finset ℕ := ([130,238,1590,1626,1644,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2714,2732,2738,2792,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4516 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4516 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4516 130 4
  · have he : independentCachedBranchMembers4516.erase 130=independentCachedBranchMembers4514 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4514
  · have he : independentCachedBranchMembers4516.filter (independentCachedEdge 130)=independentCachedBranchMembers4515 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4515
def independentCachedBranchMembers4517 : Finset ℕ := ([1678,1720,1748,1762,2620,2662,2714,2732,3118,3188,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4517 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4517 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4517 4 (fun x => (if x<2714 then (if x<1762 then (if x<1720 then 0 else (if x<1748 then 0 else 0)) else (if x<2620 then 0 else (if x<2662 then 1 else 1))) else (if x<3188 then (if x<2732 then 2 else (if x<3118 then 2 else 1)) else (if x<3282 then 1 else (if x<3300 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4518 : Finset ℕ := ([72,130,238,1590,1626,1644,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2714,2732,2738,2792,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4518 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4518 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4518 72 4
  · have he : independentCachedBranchMembers4518.erase 72=independentCachedBranchMembers4516 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4516
  · have he : independentCachedBranchMembers4518.filter (independentCachedEdge 72)=independentCachedBranchMembers4517 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4517
def independentCachedBranchMembers4519 : Finset ℕ := ([1678,1720,1748,1762,2638,2680,2738,2792,3164,3178,3222,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4519 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4519 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4519 4 (fun x => (if x<2738 then (if x<1762 then (if x<1720 then 0 else (if x<1748 then 0 else 0)) else (if x<2638 then 0 else (if x<2680 then 1 else 1))) else (if x<3178 then (if x<2792 then 2 else (if x<3164 then 2 else 1)) else (if x<3222 then 1 else (if x<3276 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4520 : Finset ℕ := ([36,72,130,238,1590,1626,1644,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2714,2732,2738,2792,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4520 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4520 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4520 36 4
  · have he : independentCachedBranchMembers4520.erase 36=independentCachedBranchMembers4518 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4518
  · have he : independentCachedBranchMembers4520.filter (independentCachedEdge 36)=independentCachedBranchMembers4519 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4519
def independentCachedBranchMembers4521 : Finset ℕ := ([36,72,130,238,1590,1626,1678,1762,2620,2638,2714,2792,3118,3164,3222,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4521 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4521 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4521 4 (fun x => (if x<2620 then (if x<1590 then (if x<130 then (if x<72 then 0 else 0) else (if x<238 then 0 else 0)) else (if x<1678 then (if x<1626 then 1 else 1) else (if x<1762 then 1 else 1))) else (if x<3118 then (if x<2714 then (if x<2638 then 2 else 2) else (if x<2792 then 2 else 2)) else (if x<3222 then (if x<3164 then 3 else 3) else (if x<3300 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4522 : Finset ℕ := ([36,72,130,238,1590,1626,1644,1650,1678,1702,1720,1738,1748,1762,2620,2638,2662,2680,2714,2732,2738,2792,3118,3164,3178,3188,3222,3276,3282,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4522 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4522 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4522 1650 4
  · have he : independentCachedBranchMembers4522.erase 1650=independentCachedBranchMembers4520 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4520
  · have he : independentCachedBranchMembers4522.filter (independentCachedEdge 1650)=independentCachedBranchMembers4521 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4521
def independentCachedBranchMembers4523 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4523 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4523 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4523 3284 5
  · have he : independentCachedBranchMembers4523.erase 3284=independentCachedBranchMembers4509 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4509
  · have he : independentCachedBranchMembers4523.filter (independentCachedEdge 3284)=independentCachedBranchMembers4522 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4522
def independentCachedBranchMembers4524 : Finset ℕ := ([1582,1628,1650,1686,1720,1738,1748,1764,2618,2646,2662,2680,2716,2732,2738,2800,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4524 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4524 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4524 5 (fun x => (if x<2716 then (if x<1748 then (if x<1686 then (if x<1628 then 0 else (if x<1650 then 0 else 0)) else (if x<1720 then 0 else (if x<1738 then 0 else 0))) else (if x<2646 then (if x<1764 then 1 else (if x<2618 then 0 else 1)) else (if x<2662 then 1 else (if x<2680 then 2 else 2)))) else (if x<3178 then (if x<2800 then (if x<2732 then 1 else (if x<2738 then 2 else 2)) else (if x<3126 then 1 else (if x<3162 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3214 then 4 else 3)) else (if x<3282 then 4 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4525 : Finset ℕ := ([1582,1628,1686,1764,2618,2646,2716,2800,3178,3188,3276,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4525 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4525 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4525 4 (fun x => (if x<2716 then (if x<1764 then (if x<1628 then 0 else (if x<1686 then 0 else 0)) else (if x<2618 then 0 else (if x<2646 then 1 else 1))) else (if x<3188 then (if x<2800 then 1 else (if x<3178 then 1 else 2)) else (if x<3276 then 2 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4526 : Finset ℕ := ([1582,1628,1650,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2716,2732,2738,2800,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4526 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4526 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4526 1702 4
  · have he : independentCachedBranchMembers4526.erase 1702=independentCachedBranchMembers4524 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4524
  · have he : independentCachedBranchMembers4526.filter (independentCachedEdge 1702)=independentCachedBranchMembers4525 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4525
def independentCachedBranchMembers4527 : Finset ℕ := ([1582,1628,1720,1738,2618,2680,2716,2732,3162,3178,3214,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4527 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4527 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4527 4 (fun x => (if x<2716 then (if x<1738 then (if x<1628 then 0 else (if x<1720 then 0 else 0)) else (if x<2618 then 0 else (if x<2680 then 1 else 2))) else (if x<3178 then (if x<2732 then 1 else (if x<3162 then 2 else 2)) else (if x<3214 then 1 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4528 : Finset ℕ := ([246,1582,1628,1650,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2716,2732,2738,2800,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4528 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4528 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4528 246 4
  · have he : independentCachedBranchMembers4528.erase 246=independentCachedBranchMembers4526 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4526
  · have he : independentCachedBranchMembers4528.filter (independentCachedEdge 246)=independentCachedBranchMembers4527 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4527
def independentCachedBranchMembers4529 : Finset ℕ := ([1582,1628,1720,1738,2646,2662,2738,2800,3126,3188,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4529 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4529 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4529 4 (fun x => (if x<2738 then (if x<1738 then (if x<1628 then 0 else (if x<1720 then 0 else 0)) else (if x<2646 then 0 else (if x<2662 then 1 else 2))) else (if x<3188 then (if x<2800 then 1 else (if x<3126 then 2 else 1)) else (if x<3282 then 2 else (if x<3298 then 1 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4530 : Finset ℕ := ([132,246,1582,1628,1650,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2716,2732,2738,2800,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4530 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4530 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4530 132 4
  · have he : independentCachedBranchMembers4530.erase 132=independentCachedBranchMembers4528 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4528
  · have he : independentCachedBranchMembers4530.filter (independentCachedEdge 132)=independentCachedBranchMembers4529 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4529
def independentCachedBranchMembers4531 : Finset ℕ := ([1686,1720,1738,1764,2618,2662,2716,2738,3126,3178,3276,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4531 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4531 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4531 4 (fun x => (if x<2716 then (if x<1764 then (if x<1720 then 0 else (if x<1738 then 0 else 0)) else (if x<2618 then 0 else (if x<2662 then 1 else 1))) else (if x<3178 then (if x<2738 then 2 else (if x<3126 then 2 else 1)) else (if x<3276 then 1 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4532 : Finset ℕ := ([80,132,246,1582,1628,1650,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2716,2732,2738,2800,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4532 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4532 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4532 80 4
  · have he : independentCachedBranchMembers4532.erase 80=independentCachedBranchMembers4530 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4530
  · have he : independentCachedBranchMembers4532.filter (independentCachedEdge 80)=independentCachedBranchMembers4531 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4531
def independentCachedBranchMembers4533 : Finset ℕ := ([1686,1720,1738,1764,2646,2680,2732,2800,3162,3188,3214,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4533 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4533 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4533 4 (fun x => (if x<2732 then (if x<1764 then (if x<1720 then 0 else (if x<1738 then 0 else 0)) else (if x<2646 then 0 else (if x<2680 then 1 else 1))) else (if x<3188 then (if x<2800 then 2 else (if x<3162 then 2 else 1)) else (if x<3214 then 1 else (if x<3282 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4534 : Finset ℕ := ([34,80,132,246,1582,1628,1650,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2716,2732,2738,2800,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4534 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4534 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4534 34 4
  · have he : independentCachedBranchMembers4534.erase 34=independentCachedBranchMembers4532 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4532
  · have he : independentCachedBranchMembers4534.filter (independentCachedEdge 34)=independentCachedBranchMembers4533 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4533
def independentCachedBranchMembers4535 : Finset ℕ := ([34,80,132,246,1582,1628,1686,1764,2618,2646,2716,2800,3126,3162,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4535 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4535 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4535 4 (fun x => (if x<2618 then (if x<1582 then (if x<132 then (if x<80 then 0 else 0) else (if x<246 then 0 else 0)) else (if x<1686 then (if x<1628 then 1 else 1) else (if x<1764 then 1 else 1))) else (if x<3126 then (if x<2716 then (if x<2646 then 2 else 2) else (if x<2800 then 2 else 2)) else (if x<3214 then (if x<3162 then 3 else 3) else (if x<3298 then 3 else 3)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4536 : Finset ℕ := ([34,80,132,246,1582,1628,1644,1650,1686,1702,1720,1738,1748,1764,2618,2646,2662,2680,2716,2732,2738,2800,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4536 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4536 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4536 1644 4
  · have he : independentCachedBranchMembers4536.erase 1644=independentCachedBranchMembers4534 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4534
  · have he : independentCachedBranchMembers4536.filter (independentCachedEdge 1644)=independentCachedBranchMembers4535 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4535
def independentCachedBranchMembers4537 : Finset ℕ := ([34,36,72,80,130,132,238,246,1582,1590,1626,1628,1644,1650,1678,1686,1702,1720,1738,1748,1762,1764,2618,2620,2638,2646,2662,2680,2714,2716,2730,2732,2738,2740,2758,2776,2792,2800,3118,3126,3162,3164,3178,3188,3214,3222,3238,3256,3274,3276,3282,3284,3298,3300] : List ℕ).toFinset
theorem independentCachedBranchBound4537 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4537 6 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4537 3274 5
  · have he : independentCachedBranchMembers4537.erase 3274=independentCachedBranchMembers4523 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4523
  · have he : independentCachedBranchMembers4537.filter (independentCachedEdge 3274)=independentCachedBranchMembers4536 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4536
def independentCachedBranchMembers4538 : Finset ℕ := ([1582,1628,1650,1686,1702,1720,1738,1764,2620,2638,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4538 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4538 5 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4538 5 (fun x => (if x<2740 then (if x<1738 then (if x<1686 then (if x<1628 then 0 else (if x<1650 then 0 else 0)) else (if x<1702 then 0 else (if x<1720 then 1 else 0))) else (if x<2638 then (if x<1764 then 0 else (if x<2620 then 0 else 2)) else (if x<2714 then 2 else (if x<2730 then 2 else 1)))) else (if x<3178 then (if x<2792 then (if x<2758 then 1 else (if x<2776 then 1 else 1)) else (if x<3126 then 2 else (if x<3162 then 3 else 3))) else (if x<3276 then (if x<3188 then 4 else (if x<3214 then 4 else 3)) else (if x<3282 then 4 else (if x<3298 then 4 else 3))))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4539 : Finset ℕ := ([1582,1628,1686,1764,2730,2740,2758,2776,3126,3162,3214,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4539 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4539 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4539 4 (fun x => (if x<2758 then (if x<1764 then (if x<1628 then 0 else (if x<1686 then 0 else 0)) else (if x<2730 then 0 else (if x<2740 then 1 else 1))) else (if x<3162 then (if x<2776 then 1 else (if x<3126 then 1 else 2)) else (if x<3214 then 2 else (if x<3298 then 2 else 2)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4540 : Finset ℕ := ([1582,1628,1644,1650,1686,1702,1720,1738,1764,2620,2638,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4540 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4540 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4540 1644 4
  · have he : independentCachedBranchMembers4540.erase 1644=independentCachedBranchMembers4538 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4538
  · have he : independentCachedBranchMembers4540.filter (independentCachedEdge 1644)=independentCachedBranchMembers4539 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4539
def independentCachedBranchMembers4541 : Finset ℕ := ([1628,1650,1686,1720,2620,2714,2740,2776,3126,3162,3188,3282] : List ℕ).toFinset
theorem independentCachedBranchBound4541 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4541 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4541 4 (fun x => (if x<2740 then (if x<1720 then (if x<1650 then 0 else (if x<1686 then 0 else 0)) else (if x<2620 then 0 else (if x<2714 then 1 else 1))) else (if x<3162 then (if x<2776 then 2 else (if x<3126 then 2 else 2)) else (if x<3188 then 2 else (if x<3282 then 1 else 1)))))
  · decide +kernel
  · decide +kernel
def independentCachedBranchMembers4542 : Finset ℕ := ([238,1582,1628,1644,1650,1686,1702,1720,1738,1764,2620,2638,2714,2730,2740,2758,2776,2792,3126,3162,3178,3188,3214,3276,3282,3298] : List ℕ).toFinset
theorem independentCachedBranchBound4542 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4542 5 := by
  apply cliqueBound_vertex_branch (fun h => independentCachedEdge_symm h) independentCachedBranchMembers4542 238 4
  · have he : independentCachedBranchMembers4542.erase 238=independentCachedBranchMembers4540 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4540
  · have he : independentCachedBranchMembers4542.filter (independentCachedEdge 238)=independentCachedBranchMembers4541 := by decide +kernel
    rw [he]
    exact independentCachedBranchBound4541
def independentCachedBranchMembers4543 : Finset ℕ := ([1582,1650,1720,1764,2638,2740,2776,2792,3126,3162,3178,3276] : List ℕ).toFinset
theorem independentCachedBranchBound4543 : ListCliqueBound independentCachedEdge independentCachedBranchMembers4543 4 := by
  apply cliqueBound_coloring_separated independentCachedBranchMembers4543 4 (fun x => (if x<2776 then (if x<1764 then (if x<1650 then 0 else (if x<1720 then 0 else 0)) else (if x<2638 then 0 else (if x<2740 then 1 else 2))) else (if x<3162 then (if x<2792 then 1 else (if x<3126 then 2 else 2)) else (if x<3178 then 1 else (if x<3276 then 2 else 1)))))
  · decide +kernel
  · decide +kernel
end EntropyDesigns.QuadraticRefinement
