/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.PlaneBranch3
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def planeBranchMembers128 : Finset ℕ := ([1642,1702,1734,2662,2762,3174,3242,3274] : List ℕ).toFinset
theorem planeBranchBound128 : ListCliqueBound encodedEdge planeBranchMembers128 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers128 3274 2
  · have he : planeBranchMembers128.erase 3274=planeBranchMembers126 := by decide
    rw [he]
    exact planeBranchBound126
  · have he : planeBranchMembers128.filter (encodedEdge 3274)=planeBranchMembers127 := by decide
    rw [he]
    exact planeBranchBound127
def planeBranchMembers129 : Finset ℕ := ([12,192,1642,1644,1702,1734,2662,2732,2762,2764,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound129 : ListCliqueBound encodedEdge planeBranchMembers129 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers129 12 3
  · have he : planeBranchMembers129.erase 12=planeBranchMembers125 := by decide
    rw [he]
    exact planeBranchBound125
  · have he : planeBranchMembers129.filter (encodedEdge 12)=planeBranchMembers128 := by decide
    rw [he]
    exact planeBranchBound128
def planeBranchMembers130 : Finset ℕ := ([12,192,1644,1734,2732,2762,3072,3174,3242,3276] : List ℕ).toFinset
theorem planeBranchBound130 : ListCliqueBound encodedEdge planeBranchMembers130 3 := by
  apply cliqueBound_coloring planeBranchMembers130 3 (fun x => match x with | 12 => 0 | 192 => 0 | 1644 => 1 | 1734 => 1 | 2732 => 2 | 2762 => 2 | 3072 => 0 | 3174 => 1 | 3242 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers131 : Finset ℕ := ([12,192,1642,1644,1702,1734,2662,2730,2732,2762,2764,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound131 : ListCliqueBound encodedEdge planeBranchMembers131 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers131 2730 3
  · have he : planeBranchMembers131.erase 2730=planeBranchMembers129 := by decide
    rw [he]
    exact planeBranchBound129
  · have he : planeBranchMembers131.filter (encodedEdge 2730)=planeBranchMembers130 := by decide
    rw [he]
    exact planeBranchBound130
def planeBranchMembers132 : Finset ℕ := ([1642,1644,1702,1734,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound132 : ListCliqueBound encodedEdge planeBranchMembers132 3 := by
  apply cliqueBound_coloring planeBranchMembers132 3 (fun x => match x with | 1642 => 0 | 1644 => 1 | 1702 => 0 | 1734 => 1 | 3072 => 2 | 3174 => 0 | 3242 => 0 | 3244 => 2 | 3274 => 2 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers133 : Finset ℕ := ([12,192,1642,1644,1702,1734,2560,2662,2730,2732,2762,2764,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound133 : ListCliqueBound encodedEdge planeBranchMembers133 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers133 2560 3
  · have he : planeBranchMembers133.erase 2560=planeBranchMembers131 := by decide
    rw [he]
    exact planeBranchBound131
  · have he : planeBranchMembers133.filter (encodedEdge 2560)=planeBranchMembers132 := by decide
    rw [he]
    exact planeBranchBound132
def planeBranchMembers134 : Finset ℕ := ([1642,1644,1734,2662,2764,3174,3274] : List ℕ).toFinset
theorem planeBranchBound134 : ListCliqueBound encodedEdge planeBranchMembers134 3 := by
  apply cliqueBound_coloring planeBranchMembers134 3 (fun x => match x with | 1642 => 0 | 1644 => 1 | 1734 => 0 | 2662 => 0 | 2764 => 1 | 3174 => 2 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers135 : Finset ℕ := ([1642,2662,2764,3274] : List ℕ).toFinset
theorem planeBranchBound135 : ListCliqueBound encodedEdge planeBranchMembers135 2 := by
  apply cliqueBound_coloring planeBranchMembers135 2 (fun x => match x with | 1642 => 0 | 2662 => 0 | 2764 => 1 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers136 : Finset ℕ := ([1642,1644,1734,2662,2764,3174,3274,3276] : List ℕ).toFinset
theorem planeBranchBound136 : ListCliqueBound encodedEdge planeBranchMembers136 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers136 3276 2
  · have he : planeBranchMembers136.erase 3276=planeBranchMembers134 := by decide
    rw [he]
    exact planeBranchBound134
  · have he : planeBranchMembers136.filter (encodedEdge 3276)=planeBranchMembers135 := by decide
    rw [he]
    exact planeBranchBound135
def planeBranchMembers137 : Finset ℕ := ([1644,2764,3174,3274] : List ℕ).toFinset
theorem planeBranchBound137 : ListCliqueBound encodedEdge planeBranchMembers137 2 := by
  apply cliqueBound_coloring planeBranchMembers137 2 (fun x => match x with | 1644 => 0 | 2764 => 0 | 3174 => 1 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers138 : Finset ℕ := ([1642,1644,1734,2662,2762,2764,3174,3274,3276] : List ℕ).toFinset
theorem planeBranchBound138 : ListCliqueBound encodedEdge planeBranchMembers138 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers138 2762 2
  · have he : planeBranchMembers138.erase 2762=planeBranchMembers136 := by decide
    rw [he]
    exact planeBranchBound136
  · have he : planeBranchMembers138.filter (encodedEdge 2762)=planeBranchMembers137 := by decide
    rw [he]
    exact planeBranchBound137
def planeBranchMembers139 : Finset ℕ := ([1642,1644,2662,3174] : List ℕ).toFinset
theorem planeBranchBound139 : ListCliqueBound encodedEdge planeBranchMembers139 2 := by
  apply cliqueBound_coloring planeBranchMembers139 2 (fun x => match x with | 1642 => 0 | 1644 => 1 | 2662 => 0 | 3174 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers140 : Finset ℕ := ([192,1642,1644,1734,2662,2762,2764,3174,3274,3276] : List ℕ).toFinset
theorem planeBranchBound140 : ListCliqueBound encodedEdge planeBranchMembers140 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers140 192 2
  · have he : planeBranchMembers140.erase 192=planeBranchMembers138 := by decide
    rw [he]
    exact planeBranchBound138
  · have he : planeBranchMembers140.filter (encodedEdge 192)=planeBranchMembers139 := by decide
    rw [he]
    exact planeBranchBound139
def planeBranchMembers141 : Finset ℕ := ([12,160,192,1642,1644,1702,1734,2560,2662,2730,2732,2762,2764,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound141 : ListCliqueBound encodedEdge planeBranchMembers141 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers141 160 3
  · have he : planeBranchMembers141.erase 160=planeBranchMembers133 := by decide
    rw [he]
    exact planeBranchBound133
  · have he : planeBranchMembers141.filter (encodedEdge 160)=planeBranchMembers140 := by decide
    rw [he]
    exact planeBranchBound140
def planeBranchMembers142 : Finset ℕ := ([1644,1702,1734,2662,2764,3174,3244] : List ℕ).toFinset
theorem planeBranchBound142 : ListCliqueBound encodedEdge planeBranchMembers142 3 := by
  apply cliqueBound_coloring planeBranchMembers142 3 (fun x => match x with | 1644 => 0 | 1702 => 0 | 1734 => 1 | 2662 => 0 | 2764 => 1 | 3174 => 2 | 3244 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers143 : Finset ℕ := ([1702,2662,2764,3244] : List ℕ).toFinset
theorem planeBranchBound143 : ListCliqueBound encodedEdge planeBranchMembers143 2 := by
  apply cliqueBound_coloring planeBranchMembers143 2 (fun x => match x with | 1702 => 0 | 2662 => 0 | 2764 => 1 | 3244 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers144 : Finset ℕ := ([1644,1702,1734,2662,2764,3174,3244,3276] : List ℕ).toFinset
theorem planeBranchBound144 : ListCliqueBound encodedEdge planeBranchMembers144 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers144 3276 2
  · have he : planeBranchMembers144.erase 3276=planeBranchMembers142 := by decide
    rw [he]
    exact planeBranchBound142
  · have he : planeBranchMembers144.filter (encodedEdge 3276)=planeBranchMembers143 := by decide
    rw [he]
    exact planeBranchBound143
def planeBranchMembers145 : Finset ℕ := ([1734,2764,3174,3244] : List ℕ).toFinset
theorem planeBranchBound145 : ListCliqueBound encodedEdge planeBranchMembers145 2 := by
  apply cliqueBound_coloring planeBranchMembers145 2 (fun x => match x with | 1734 => 0 | 2764 => 0 | 3174 => 1 | 3244 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers146 : Finset ℕ := ([1644,1702,1734,2662,2732,2764,3174,3244,3276] : List ℕ).toFinset
theorem planeBranchBound146 : ListCliqueBound encodedEdge planeBranchMembers146 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers146 2732 2
  · have he : planeBranchMembers146.erase 2732=planeBranchMembers144 := by decide
    rw [he]
    exact planeBranchBound144
  · have he : planeBranchMembers146.filter (encodedEdge 2732)=planeBranchMembers145 := by decide
    rw [he]
    exact planeBranchBound145
def planeBranchMembers147 : Finset ℕ := ([1702,1734,2662,3174] : List ℕ).toFinset
theorem planeBranchBound147 : ListCliqueBound encodedEdge planeBranchMembers147 2 := by
  apply cliqueBound_coloring planeBranchMembers147 2 (fun x => match x with | 1702 => 0 | 1734 => 1 | 2662 => 0 | 3174 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers148 : Finset ℕ := ([12,1644,1702,1734,2662,2732,2764,3174,3244,3276] : List ℕ).toFinset
theorem planeBranchBound148 : ListCliqueBound encodedEdge planeBranchMembers148 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers148 12 2
  · have he : planeBranchMembers148.erase 12=planeBranchMembers146 := by decide
    rw [he]
    exact planeBranchBound146
  · have he : planeBranchMembers148.filter (encodedEdge 12)=planeBranchMembers147 := by decide
    rw [he]
    exact planeBranchBound147
def planeBranchMembers149 : Finset ℕ := ([10,12,160,192,1642,1644,1702,1734,2560,2662,2730,2732,2762,2764,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound149 : ListCliqueBound encodedEdge planeBranchMembers149 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers149 10 3
  · have he : planeBranchMembers149.erase 10=planeBranchMembers141 := by decide
    rw [he]
    exact planeBranchBound141
  · have he : planeBranchMembers149.filter (encodedEdge 10)=planeBranchMembers148 := by decide
    rw [he]
    exact planeBranchBound148
def planeBranchMembers150 : Finset ℕ := ([10,12,160,192,1638,1642,1644,1702,1706,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound150 : ListCliqueBound encodedEdge planeBranchMembers150 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers150 1638 4
  · have he : planeBranchMembers150.erase 1638=planeBranchMembers120 := by decide
    rw [he]
    exact planeBranchBound120
  · have he : planeBranchMembers150.filter (encodedEdge 1638)=planeBranchMembers149 := by decide
    rw [he]
    exact planeBranchBound149
def planeBranchMembers151 : Finset ℕ := ([2732,2762,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound151 : ListCliqueBound encodedEdge planeBranchMembers151 4 := by
  apply cliqueBound_coloring planeBranchMembers151 4 (fun x => match x with | 2732 => 0 | 2762 => 0 | 3072 => 1 | 3174 => 1 | 3178 => 2 | 3180 => 3 | 3238 => 2 | 3242 => 0 | 3244 => 1 | 3270 => 3 | 3274 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers152 : Finset ℕ := ([2762,3072,3178,3180,3242,3244,3270] : List ℕ).toFinset
theorem planeBranchBound152 : ListCliqueBound encodedEdge planeBranchMembers152 3 := by
  apply cliqueBound_coloring planeBranchMembers152 3 (fun x => match x with | 2762 => 0 | 3072 => 1 | 3178 => 0 | 3180 => 1 | 3242 => 1 | 3244 => 2 | 3270 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers153 : Finset ℕ := ([2732,2758,2762,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound153 : ListCliqueBound encodedEdge planeBranchMembers153 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers153 2758 3
  · have he : planeBranchMembers153.erase 2758=planeBranchMembers151 := by decide
    rw [he]
    exact planeBranchBound151
  · have he : planeBranchMembers153.filter (encodedEdge 2758)=planeBranchMembers152 := by decide
    rw [he]
    exact planeBranchBound152
def planeBranchMembers154 : Finset ℕ := ([2732,3072,3180,3238,3242,3270,3274] : List ℕ).toFinset
theorem planeBranchBound154 : ListCliqueBound encodedEdge planeBranchMembers154 3 := by
  apply cliqueBound_coloring planeBranchMembers154 3 (fun x => match x with | 2732 => 0 | 3072 => 1 | 3180 => 0 | 3238 => 0 | 3242 => 1 | 3270 => 1 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers155 : Finset ℕ := ([2668,2732,2758,2762,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound155 : ListCliqueBound encodedEdge planeBranchMembers155 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers155 2668 3
  · have he : planeBranchMembers155.erase 2668=planeBranchMembers153 := by decide
    rw [he]
    exact planeBranchBound153
  · have he : planeBranchMembers155.filter (encodedEdge 2668)=planeBranchMembers154 := by decide
    rw [he]
    exact planeBranchBound154
def planeBranchMembers156 : Finset ℕ := ([2732,2758,3072,3178,3180,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound156 : ListCliqueBound encodedEdge planeBranchMembers156 3 := by
  apply cliqueBound_coloring planeBranchMembers156 3 (fun x => match x with | 2732 => 0 | 2758 => 0 | 3072 => 1 | 3178 => 1 | 3180 => 2 | 3238 => 0 | 3274 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers157 : Finset ℕ := ([2668,2726,2732,2758,2762,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound157 : ListCliqueBound encodedEdge planeBranchMembers157 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers157 2726 3
  · have he : planeBranchMembers157.erase 2726=planeBranchMembers155 := by decide
    rw [he]
    exact planeBranchBound155
  · have he : planeBranchMembers157.filter (encodedEdge 2726)=planeBranchMembers156 := by decide
    rw [he]
    exact planeBranchBound156
def planeBranchMembers158 : Finset ℕ := ([2668,2762,3072,3178,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound158 : ListCliqueBound encodedEdge planeBranchMembers158 3 := by
  apply cliqueBound_coloring planeBranchMembers158 3 (fun x => match x with | 2668 => 0 | 2762 => 0 | 3072 => 1 | 3178 => 0 | 3238 => 1 | 3244 => 2 | 3270 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers159 : Finset ℕ := ([2666,2668,2726,2732,2758,2762,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound159 : ListCliqueBound encodedEdge planeBranchMembers159 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers159 2666 3
  · have he : planeBranchMembers159.erase 2666=planeBranchMembers157 := by decide
    rw [he]
    exact planeBranchBound157
  · have he : planeBranchMembers159.filter (encodedEdge 2666)=planeBranchMembers158 := by decide
    rw [he]
    exact planeBranchBound158
end EntropyDesigns.QuadraticRefinement
