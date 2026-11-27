/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.PlaneBranch2
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def planeBranchMembers96 : Finset ℕ := ([12,192,1642,1644,1702,1706,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound96 : ListCliqueBound encodedEdge planeBranchMembers96 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers96 1706 4
  · have he : planeBranchMembers96.erase 1706=planeBranchMembers82 := by decide
    rw [he]
    exact planeBranchBound82
  · have he : planeBranchMembers96.filter (encodedEdge 1706)=planeBranchMembers95 := by decide
    rw [he]
    exact planeBranchBound95
def planeBranchMembers97 : Finset ℕ := ([192,1644,1734,1738,2662,2758,2762,2764,3174,3178,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound97 : ListCliqueBound encodedEdge planeBranchMembers97 4 := by
  apply cliqueBound_coloring planeBranchMembers97 4 (fun x => match x with | 192 => 0 | 1644 => 1 | 1734 => 0 | 1738 => 1 | 2662 => 2 | 2758 => 3 | 2762 => 0 | 2764 => 1 | 3174 => 3 | 3178 => 2 | 3270 => 2 | 3274 => 3 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers98 : Finset ℕ := ([192,1644,1734,1738,2662,2764,3270,3274] : List ℕ).toFinset
theorem planeBranchBound98 : ListCliqueBound encodedEdge planeBranchMembers98 3 := by
  apply cliqueBound_coloring planeBranchMembers98 3 (fun x => match x with | 192 => 0 | 1644 => 1 | 1734 => 0 | 1738 => 1 | 2662 => 2 | 2764 => 0 | 3270 => 2 | 3274 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers99 : Finset ℕ := ([192,1644,1734,1738,2662,2668,2758,2762,2764,3174,3178,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound99 : ListCliqueBound encodedEdge planeBranchMembers99 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers99 2668 3
  · have he : planeBranchMembers99.erase 2668=planeBranchMembers97 := by decide
    rw [he]
    exact planeBranchBound97
  · have he : planeBranchMembers99.filter (encodedEdge 2668)=planeBranchMembers98 := by decide
    rw [he]
    exact planeBranchBound98
def planeBranchMembers100 : Finset ℕ := ([1644,1734,1738,2662,2764,3174,3178,3276] : List ℕ).toFinset
theorem planeBranchBound100 : ListCliqueBound encodedEdge planeBranchMembers100 3 := by
  apply cliqueBound_coloring planeBranchMembers100 3 (fun x => match x with | 1644 => 0 | 1734 => 0 | 1738 => 1 | 2662 => 0 | 2764 => 0 | 3174 => 2 | 3178 => 1 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers101 : Finset ℕ := ([192,1644,1734,1738,1740,2662,2668,2758,2762,2764,3174,3178,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound101 : ListCliqueBound encodedEdge planeBranchMembers101 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers101 1740 3
  · have he : planeBranchMembers101.erase 1740=planeBranchMembers99 := by decide
    rw [he]
    exact planeBranchBound99
  · have he : planeBranchMembers101.filter (encodedEdge 1740)=planeBranchMembers100 := by decide
    rw [he]
    exact planeBranchBound100
def planeBranchMembers102 : Finset ℕ := ([192,1644,1738,2758,2764,3178,3270,3276] : List ℕ).toFinset
theorem planeBranchBound102 : ListCliqueBound encodedEdge planeBranchMembers102 3 := by
  apply cliqueBound_coloring planeBranchMembers102 3 (fun x => match x with | 192 => 0 | 1644 => 1 | 1738 => 0 | 2758 => 0 | 2764 => 1 | 3178 => 2 | 3270 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers103 : Finset ℕ := ([192,1642,1644,1734,1738,1740,2662,2668,2758,2762,2764,3174,3178,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound103 : ListCliqueBound encodedEdge planeBranchMembers103 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers103 1642 3
  · have he : planeBranchMembers103.erase 1642=planeBranchMembers101 := by decide
    rw [he]
    exact planeBranchBound101
  · have he : planeBranchMembers103.filter (encodedEdge 1642)=planeBranchMembers102 := by decide
    rw [he]
    exact planeBranchBound102
def planeBranchMembers104 : Finset ℕ := ([192,1644,1734,1738,2668,2758,2762,3174,3178,3276] : List ℕ).toFinset
theorem planeBranchBound104 : ListCliqueBound encodedEdge planeBranchMembers104 3 := by
  apply cliqueBound_coloring planeBranchMembers104 3 (fun x => match x with | 192 => 0 | 1644 => 1 | 1734 => 0 | 1738 => 1 | 2668 => 2 | 2758 => 2 | 2762 => 0 | 3174 => 2 | 3178 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers105 : Finset ℕ := ([192,1642,1644,1734,1738,1740,2662,2668,2758,2762,2764,3174,3178,3180,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound105 : ListCliqueBound encodedEdge planeBranchMembers105 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers105 3180 3
  · have he : planeBranchMembers105.erase 3180=planeBranchMembers103 := by decide
    rw [he]
    exact planeBranchBound103
  · have he : planeBranchMembers105.filter (encodedEdge 3180)=planeBranchMembers104 := by decide
    rw [he]
    exact planeBranchBound104
def planeBranchMembers106 : Finset ℕ := ([192,1642,1734,1740,2662,2668,2762,3178,3270,3276] : List ℕ).toFinset
theorem planeBranchBound106 : ListCliqueBound encodedEdge planeBranchMembers106 3 := by
  apply cliqueBound_coloring planeBranchMembers106 3 (fun x => match x with | 192 => 0 | 1642 => 1 | 1734 => 0 | 1740 => 1 | 2662 => 2 | 2668 => 1 | 2762 => 0 | 3178 => 2 | 3270 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers107 : Finset ℕ := ([192,1642,1644,1734,1738,1740,2662,2666,2668,2758,2762,2764,3174,3178,3180,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound107 : ListCliqueBound encodedEdge planeBranchMembers107 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers107 2666 3
  · have he : planeBranchMembers107.erase 2666=planeBranchMembers105 := by decide
    rw [he]
    exact planeBranchBound105
  · have he : planeBranchMembers107.filter (encodedEdge 2666)=planeBranchMembers106 := by decide
    rw [he]
    exact planeBranchBound106
def planeBranchMembers108 : Finset ℕ := ([12,160,192,1642,1644,1702,1706,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound108 : ListCliqueBound encodedEdge planeBranchMembers108 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers108 160 4
  · have he : planeBranchMembers108.erase 160=planeBranchMembers96 := by decide
    rw [he]
    exact planeBranchBound96
  · have he : planeBranchMembers108.filter (encodedEdge 160)=planeBranchMembers107 := by decide
    rw [he]
    exact planeBranchBound107
def planeBranchMembers109 : Finset ℕ := ([12,1644,1708,1734,2662,2668,2732,2764,3174,3180,3238,3244,3276] : List ℕ).toFinset
theorem planeBranchBound109 : ListCliqueBound encodedEdge planeBranchMembers109 4 := by
  apply cliqueBound_coloring planeBranchMembers109 4 (fun x => match x with | 12 => 0 | 1644 => 0 | 1708 => 1 | 1734 => 1 | 2662 => 2 | 2668 => 3 | 2732 => 0 | 2764 => 1 | 3174 => 3 | 3180 => 2 | 3238 => 2 | 3244 => 3 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers110 : Finset ℕ := ([12,1644,1708,1734,2662,2764,3180,3244] : List ℕ).toFinset
theorem planeBranchBound110 : ListCliqueBound encodedEdge planeBranchMembers110 3 := by
  apply cliqueBound_coloring planeBranchMembers110 3 (fun x => match x with | 12 => 0 | 1644 => 0 | 1708 => 1 | 1734 => 1 | 2662 => 2 | 2764 => 0 | 3180 => 2 | 3244 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers111 : Finset ℕ := ([12,1644,1708,1734,2662,2668,2732,2758,2764,3174,3180,3238,3244,3276] : List ℕ).toFinset
theorem planeBranchBound111 : ListCliqueBound encodedEdge planeBranchMembers111 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers111 2758 3
  · have he : planeBranchMembers111.erase 2758=planeBranchMembers109 := by decide
    rw [he]
    exact planeBranchBound109
  · have he : planeBranchMembers111.filter (encodedEdge 2758)=planeBranchMembers110 := by decide
    rw [he]
    exact planeBranchBound110
def planeBranchMembers112 : Finset ℕ := ([1644,1708,1734,2662,2764,3174,3238,3276] : List ℕ).toFinset
theorem planeBranchBound112 : ListCliqueBound encodedEdge planeBranchMembers112 3 := by
  apply cliqueBound_coloring planeBranchMembers112 3 (fun x => match x with | 1644 => 0 | 1708 => 1 | 1734 => 0 | 2662 => 0 | 2764 => 0 | 3174 => 2 | 3238 => 1 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers113 : Finset ℕ := ([12,1644,1708,1734,1740,2662,2668,2732,2758,2764,3174,3180,3238,3244,3276] : List ℕ).toFinset
theorem planeBranchBound113 : ListCliqueBound encodedEdge planeBranchMembers113 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers113 1740 3
  · have he : planeBranchMembers113.erase 1740=planeBranchMembers111 := by decide
    rw [he]
    exact planeBranchBound111
  · have he : planeBranchMembers113.filter (encodedEdge 1740)=planeBranchMembers112 := by decide
    rw [he]
    exact planeBranchBound112
def planeBranchMembers114 : Finset ℕ := ([12,1708,1734,2668,2764,3180,3238,3276] : List ℕ).toFinset
theorem planeBranchBound114 : ListCliqueBound encodedEdge planeBranchMembers114 3 := by
  apply cliqueBound_coloring planeBranchMembers114 3 (fun x => match x with | 12 => 0 | 1708 => 0 | 1734 => 1 | 2668 => 0 | 2764 => 1 | 3180 => 2 | 3238 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers115 : Finset ℕ := ([12,1644,1702,1708,1734,1740,2662,2668,2732,2758,2764,3174,3180,3238,3244,3276] : List ℕ).toFinset
theorem planeBranchBound115 : ListCliqueBound encodedEdge planeBranchMembers115 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers115 1702 3
  · have he : planeBranchMembers115.erase 1702=planeBranchMembers113 := by decide
    rw [he]
    exact planeBranchBound113
  · have he : planeBranchMembers115.filter (encodedEdge 1702)=planeBranchMembers114 := by decide
    rw [he]
    exact planeBranchBound114
def planeBranchMembers116 : Finset ℕ := ([12,1644,1708,1734,2668,2732,2758,3174,3238,3276] : List ℕ).toFinset
theorem planeBranchBound116 : ListCliqueBound encodedEdge planeBranchMembers116 3 := by
  apply cliqueBound_coloring planeBranchMembers116 3 (fun x => match x with | 12 => 0 | 1644 => 0 | 1708 => 1 | 1734 => 1 | 2668 => 2 | 2732 => 0 | 2758 => 2 | 3174 => 2 | 3238 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers117 : Finset ℕ := ([12,1644,1702,1708,1734,1740,2662,2668,2732,2758,2764,3174,3180,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound117 : ListCliqueBound encodedEdge planeBranchMembers117 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers117 3270 3
  · have he : planeBranchMembers117.erase 3270=planeBranchMembers115 := by decide
    rw [he]
    exact planeBranchBound115
  · have he : planeBranchMembers117.filter (encodedEdge 3270)=planeBranchMembers116 := by decide
    rw [he]
    exact planeBranchBound116
def planeBranchMembers118 : Finset ℕ := ([12,1644,1702,1740,2662,2732,2758,3180,3238,3276] : List ℕ).toFinset
theorem planeBranchBound118 : ListCliqueBound encodedEdge planeBranchMembers118 3 := by
  apply cliqueBound_coloring planeBranchMembers118 3 (fun x => match x with | 12 => 0 | 1644 => 0 | 1702 => 1 | 1740 => 1 | 2662 => 2 | 2732 => 0 | 2758 => 1 | 3180 => 2 | 3238 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers119 : Finset ℕ := ([12,1644,1702,1708,1734,1740,2662,2668,2726,2732,2758,2764,3174,3180,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound119 : ListCliqueBound encodedEdge planeBranchMembers119 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers119 2726 3
  · have he : planeBranchMembers119.erase 2726=planeBranchMembers117 := by decide
    rw [he]
    exact planeBranchBound117
  · have he : planeBranchMembers119.filter (encodedEdge 2726)=planeBranchMembers118 := by decide
    rw [he]
    exact planeBranchBound118
def planeBranchMembers120 : Finset ℕ := ([10,12,160,192,1642,1644,1702,1706,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound120 : ListCliqueBound encodedEdge planeBranchMembers120 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers120 10 4
  · have he : planeBranchMembers120.erase 10=planeBranchMembers108 := by decide
    rw [he]
    exact planeBranchBound108
  · have he : planeBranchMembers120.filter (encodedEdge 10)=planeBranchMembers119 := by decide
    rw [he]
    exact planeBranchBound119
def planeBranchMembers121 : Finset ℕ := ([1642,1644,1702,1734,2662,2732,2762,2764,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound121 : ListCliqueBound encodedEdge planeBranchMembers121 4 := by
  apply cliqueBound_coloring planeBranchMembers121 4 (fun x => match x with | 1642 => 0 | 1644 => 1 | 1702 => 0 | 1734 => 1 | 2662 => 0 | 2732 => 2 | 2762 => 2 | 2764 => 1 | 3072 => 3 | 3174 => 3 | 3242 => 2 | 3244 => 3 | 3274 => 3 | 3276 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers122 : Finset ℕ := ([1642,1644,1702,2662,2732,3174,3242] : List ℕ).toFinset
theorem planeBranchBound122 : ListCliqueBound encodedEdge planeBranchMembers122 3 := by
  apply cliqueBound_coloring planeBranchMembers122 3 (fun x => match x with | 1642 => 0 | 1644 => 1 | 1702 => 0 | 2662 => 0 | 2732 => 1 | 3174 => 2 | 3242 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers123 : Finset ℕ := ([1642,2662,2732,3242] : List ℕ).toFinset
theorem planeBranchBound123 : ListCliqueBound encodedEdge planeBranchMembers123 2 := by
  apply cliqueBound_coloring planeBranchMembers123 2 (fun x => match x with | 1642 => 0 | 2662 => 0 | 2732 => 1 | 3242 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers124 : Finset ℕ := ([1642,1644,1702,2662,2732,3174,3242,3244] : List ℕ).toFinset
theorem planeBranchBound124 : ListCliqueBound encodedEdge planeBranchMembers124 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers124 3244 2
  · have he : planeBranchMembers124.erase 3244=planeBranchMembers122 := by decide
    rw [he]
    exact planeBranchBound122
  · have he : planeBranchMembers124.filter (encodedEdge 3244)=planeBranchMembers123 := by decide
    rw [he]
    exact planeBranchBound123
def planeBranchMembers125 : Finset ℕ := ([192,1642,1644,1702,1734,2662,2732,2762,2764,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound125 : ListCliqueBound encodedEdge planeBranchMembers125 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers125 192 3
  · have he : planeBranchMembers125.erase 192=planeBranchMembers121 := by decide
    rw [he]
    exact planeBranchBound121
  · have he : planeBranchMembers125.filter (encodedEdge 192)=planeBranchMembers124 := by decide
    rw [he]
    exact planeBranchBound124
def planeBranchMembers126 : Finset ℕ := ([1642,1702,1734,2662,2762,3174,3242] : List ℕ).toFinset
theorem planeBranchBound126 : ListCliqueBound encodedEdge planeBranchMembers126 3 := by
  apply cliqueBound_coloring planeBranchMembers126 3 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1734 => 1 | 2662 => 0 | 2762 => 1 | 3174 => 2 | 3242 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers127 : Finset ℕ := ([1702,2662,2762,3242] : List ℕ).toFinset
theorem planeBranchBound127 : ListCliqueBound encodedEdge planeBranchMembers127 2 := by
  apply cliqueBound_coloring planeBranchMembers127 2 (fun x => match x with | 1702 => 0 | 2662 => 0 | 2762 => 1 | 3242 => 1 | _ => 0)
  · decide
  · decide
end EntropyDesigns.QuadraticRefinement
