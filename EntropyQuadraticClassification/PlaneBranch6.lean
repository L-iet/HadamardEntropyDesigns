/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.PlaneBranch5
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def planeBranchMembers192 : Finset ℕ := ([192,1734,1738,1740,2758,2762,2764,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound192 : ListCliqueBound encodedEdge planeBranchMembers192 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers192 1734 2
  · have he : planeBranchMembers192.erase 1734=planeBranchMembers190 := by decide
    rw [he]
    exact planeBranchBound190
  · have he : planeBranchMembers192.filter (encodedEdge 1734)=planeBranchMembers191 := by decide
    rw [he]
    exact planeBranchBound191
def planeBranchMembers193 : Finset ℕ := ([160,192,1702,1706,1708,1734,1738,1740,2726,2730,2732,2758,2762,2764,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound193 : ListCliqueBound encodedEdge planeBranchMembers193 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers193 160 3
  · have he : planeBranchMembers193.erase 160=planeBranchMembers189 := by decide
    rw [he]
    exact planeBranchBound189
  · have he : planeBranchMembers193.filter (encodedEdge 160)=planeBranchMembers192 := by decide
    rw [he]
    exact planeBranchBound192
def planeBranchMembers194 : Finset ℕ := ([10,12,96,160,192,1536,1638,1642,1644,1702,1706,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound194 : ListCliqueBound encodedEdge planeBranchMembers194 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers194 96 4
  · have he : planeBranchMembers194.erase 96=planeBranchMembers170 := by decide
    rw [he]
    exact planeBranchBound170
  · have he : planeBranchMembers194.filter (encodedEdge 96)=planeBranchMembers193 := by decide
    rw [he]
    exact planeBranchBound193
def planeBranchMembers195 : Finset ℕ := ([12,1644,1708,1738,2666,2668,2732,2764,3178,3180,3242,3244,3276] : List ℕ).toFinset
theorem planeBranchBound195 : ListCliqueBound encodedEdge planeBranchMembers195 4 := by
  apply cliqueBound_coloring planeBranchMembers195 4 (fun x => match x with | 12 => 0 | 1644 => 0 | 1708 => 1 | 1738 => 1 | 2666 => 2 | 2668 => 3 | 2732 => 0 | 2764 => 1 | 3178 => 3 | 3180 => 2 | 3242 => 2 | 3244 => 3 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers196 : Finset ℕ := ([12,1644,1708,1738,2666,2764,3180,3244] : List ℕ).toFinset
theorem planeBranchBound196 : ListCliqueBound encodedEdge planeBranchMembers196 3 := by
  apply cliqueBound_coloring planeBranchMembers196 3 (fun x => match x with | 12 => 0 | 1644 => 0 | 1708 => 1 | 1738 => 1 | 2666 => 2 | 2764 => 0 | 3180 => 2 | 3244 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers197 : Finset ℕ := ([12,1644,1708,1738,2666,2668,2732,2762,2764,3178,3180,3242,3244,3276] : List ℕ).toFinset
theorem planeBranchBound197 : ListCliqueBound encodedEdge planeBranchMembers197 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers197 2762 3
  · have he : planeBranchMembers197.erase 2762=planeBranchMembers195 := by decide
    rw [he]
    exact planeBranchBound195
  · have he : planeBranchMembers197.filter (encodedEdge 2762)=planeBranchMembers196 := by decide
    rw [he]
    exact planeBranchBound196
def planeBranchMembers198 : Finset ℕ := ([1644,1708,1738,2666,2764,3178,3242,3276] : List ℕ).toFinset
theorem planeBranchBound198 : ListCliqueBound encodedEdge planeBranchMembers198 3 := by
  apply cliqueBound_coloring planeBranchMembers198 3 (fun x => match x with | 1644 => 0 | 1708 => 1 | 1738 => 0 | 2666 => 0 | 2764 => 0 | 3178 => 2 | 3242 => 1 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers199 : Finset ℕ := ([12,1644,1708,1738,1740,2666,2668,2732,2762,2764,3178,3180,3242,3244,3276] : List ℕ).toFinset
theorem planeBranchBound199 : ListCliqueBound encodedEdge planeBranchMembers199 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers199 1740 3
  · have he : planeBranchMembers199.erase 1740=planeBranchMembers197 := by decide
    rw [he]
    exact planeBranchBound197
  · have he : planeBranchMembers199.filter (encodedEdge 1740)=planeBranchMembers198 := by decide
    rw [he]
    exact planeBranchBound198
def planeBranchMembers200 : Finset ℕ := ([12,1708,1738,2668,2764,3180,3242,3276] : List ℕ).toFinset
theorem planeBranchBound200 : ListCliqueBound encodedEdge planeBranchMembers200 3 := by
  apply cliqueBound_coloring planeBranchMembers200 3 (fun x => match x with | 12 => 0 | 1708 => 0 | 1738 => 1 | 2668 => 0 | 2764 => 1 | 3180 => 2 | 3242 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers201 : Finset ℕ := ([12,1644,1706,1708,1738,1740,2666,2668,2732,2762,2764,3178,3180,3242,3244,3276] : List ℕ).toFinset
theorem planeBranchBound201 : ListCliqueBound encodedEdge planeBranchMembers201 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers201 1706 3
  · have he : planeBranchMembers201.erase 1706=planeBranchMembers199 := by decide
    rw [he]
    exact planeBranchBound199
  · have he : planeBranchMembers201.filter (encodedEdge 1706)=planeBranchMembers200 := by decide
    rw [he]
    exact planeBranchBound200
def planeBranchMembers202 : Finset ℕ := ([12,1644,1708,1738,2668,2732,2762,3178,3242,3276] : List ℕ).toFinset
theorem planeBranchBound202 : ListCliqueBound encodedEdge planeBranchMembers202 3 := by
  apply cliqueBound_coloring planeBranchMembers202 3 (fun x => match x with | 12 => 0 | 1644 => 0 | 1708 => 1 | 1738 => 1 | 2668 => 2 | 2732 => 0 | 2762 => 2 | 3178 => 2 | 3242 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers203 : Finset ℕ := ([12,1644,1706,1708,1738,1740,2666,2668,2732,2762,2764,3178,3180,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound203 : ListCliqueBound encodedEdge planeBranchMembers203 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers203 3274 3
  · have he : planeBranchMembers203.erase 3274=planeBranchMembers201 := by decide
    rw [he]
    exact planeBranchBound201
  · have he : planeBranchMembers203.filter (encodedEdge 3274)=planeBranchMembers202 := by decide
    rw [he]
    exact planeBranchBound202
def planeBranchMembers204 : Finset ℕ := ([12,1644,1706,1740,2666,2732,2762,3180,3242,3276] : List ℕ).toFinset
theorem planeBranchBound204 : ListCliqueBound encodedEdge planeBranchMembers204 3 := by
  apply cliqueBound_coloring planeBranchMembers204 3 (fun x => match x with | 12 => 0 | 1644 => 0 | 1706 => 1 | 1740 => 1 | 2666 => 2 | 2732 => 0 | 2762 => 1 | 3180 => 2 | 3242 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers205 : Finset ℕ := ([12,1644,1706,1708,1738,1740,2666,2668,2730,2732,2762,2764,3178,3180,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound205 : ListCliqueBound encodedEdge planeBranchMembers205 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers205 2730 3
  · have he : planeBranchMembers205.erase 2730=planeBranchMembers203 := by decide
    rw [he]
    exact planeBranchBound203
  · have he : planeBranchMembers205.filter (encodedEdge 2730)=planeBranchMembers204 := by decide
    rw [he]
    exact planeBranchBound204
def planeBranchMembers206 : Finset ℕ := ([1644,1706,1738,2666,2764,3178,3244] : List ℕ).toFinset
theorem planeBranchBound206 : ListCliqueBound encodedEdge planeBranchMembers206 3 := by
  apply cliqueBound_coloring planeBranchMembers206 3 (fun x => match x with | 1644 => 0 | 1706 => 0 | 1738 => 1 | 2666 => 0 | 2764 => 1 | 3178 => 2 | 3244 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers207 : Finset ℕ := ([1706,2666,2764,3244] : List ℕ).toFinset
theorem planeBranchBound207 : ListCliqueBound encodedEdge planeBranchMembers207 2 := by
  apply cliqueBound_coloring planeBranchMembers207 2 (fun x => match x with | 1706 => 0 | 2666 => 0 | 2764 => 1 | 3244 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers208 : Finset ℕ := ([1644,1706,1738,2666,2764,3178,3244,3276] : List ℕ).toFinset
theorem planeBranchBound208 : ListCliqueBound encodedEdge planeBranchMembers208 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers208 3276 2
  · have he : planeBranchMembers208.erase 3276=planeBranchMembers206 := by decide
    rw [he]
    exact planeBranchBound206
  · have he : planeBranchMembers208.filter (encodedEdge 3276)=planeBranchMembers207 := by decide
    rw [he]
    exact planeBranchBound207
def planeBranchMembers209 : Finset ℕ := ([1738,2764,3178,3244] : List ℕ).toFinset
theorem planeBranchBound209 : ListCliqueBound encodedEdge planeBranchMembers209 2 := by
  apply cliqueBound_coloring planeBranchMembers209 2 (fun x => match x with | 1738 => 0 | 2764 => 0 | 3178 => 1 | 3244 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers210 : Finset ℕ := ([1644,1706,1738,2666,2732,2764,3178,3244,3276] : List ℕ).toFinset
theorem planeBranchBound210 : ListCliqueBound encodedEdge planeBranchMembers210 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers210 2732 2
  · have he : planeBranchMembers210.erase 2732=planeBranchMembers208 := by decide
    rw [he]
    exact planeBranchBound208
  · have he : planeBranchMembers210.filter (encodedEdge 2732)=planeBranchMembers209 := by decide
    rw [he]
    exact planeBranchBound209
def planeBranchMembers211 : Finset ℕ := ([1706,1738,2666,3178] : List ℕ).toFinset
theorem planeBranchBound211 : ListCliqueBound encodedEdge planeBranchMembers211 2 := by
  apply cliqueBound_coloring planeBranchMembers211 2 (fun x => match x with | 1706 => 0 | 1738 => 1 | 2666 => 0 | 3178 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers212 : Finset ℕ := ([12,1644,1706,1738,2666,2732,2764,3178,3244,3276] : List ℕ).toFinset
theorem planeBranchBound212 : ListCliqueBound encodedEdge planeBranchMembers212 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers212 12 2
  · have he : planeBranchMembers212.erase 12=planeBranchMembers210 := by decide
    rw [he]
    exact planeBranchBound210
  · have he : planeBranchMembers212.filter (encodedEdge 12)=planeBranchMembers211 := by decide
    rw [he]
    exact planeBranchBound211
def planeBranchMembers213 : Finset ℕ := ([12,1642,1644,1706,1708,1738,1740,2666,2668,2730,2732,2762,2764,3178,3180,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound213 : ListCliqueBound encodedEdge planeBranchMembers213 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers213 1642 3
  · have he : planeBranchMembers213.erase 1642=planeBranchMembers205 := by decide
    rw [he]
    exact planeBranchBound205
  · have he : planeBranchMembers213.filter (encodedEdge 1642)=planeBranchMembers212 := by decide
    rw [he]
    exact planeBranchBound212
def planeBranchMembers214 : Finset ℕ := ([12,1708,1740,2668,2732,2764,3180,3244,3276] : List ℕ).toFinset
theorem planeBranchBound214 : ListCliqueBound encodedEdge planeBranchMembers214 3 := by
  apply cliqueBound_coloring planeBranchMembers214 3 (fun x => match x with | 12 => 0 | 1708 => 0 | 1740 => 1 | 2668 => 0 | 2732 => 1 | 2764 => 2 | 3180 => 1 | 3244 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers215 : Finset ℕ := ([1708,1740,2668,3180] : List ℕ).toFinset
theorem planeBranchBound215 : ListCliqueBound encodedEdge planeBranchMembers215 2 := by
  apply cliqueBound_coloring planeBranchMembers215 2 (fun x => match x with | 1708 => 0 | 1740 => 1 | 2668 => 0 | 3180 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers216 : Finset ℕ := ([12,1644,1708,1740,2668,2732,2764,3180,3244,3276] : List ℕ).toFinset
theorem planeBranchBound216 : ListCliqueBound encodedEdge planeBranchMembers216 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers216 1644 2
  · have he : planeBranchMembers216.erase 1644=planeBranchMembers214 := by decide
    rw [he]
    exact planeBranchBound214
  · have he : planeBranchMembers216.filter (encodedEdge 1644)=planeBranchMembers215 := by decide
    rw [he]
    exact planeBranchBound215
def planeBranchMembers217 : Finset ℕ := ([10,12,1642,1644,1706,1708,1738,1740,2666,2668,2730,2732,2762,2764,3178,3180,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound217 : ListCliqueBound encodedEdge planeBranchMembers217 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers217 10 3
  · have he : planeBranchMembers217.erase 10=planeBranchMembers213 := by decide
    rw [he]
    exact planeBranchBound213
  · have he : planeBranchMembers217.filter (encodedEdge 10)=planeBranchMembers216 := by decide
    rw [he]
    exact planeBranchBound216
def planeBranchMembers218 : Finset ℕ := ([6,10,12,96,160,192,1536,1638,1642,1644,1702,1706,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound218 : ListCliqueBound encodedEdge planeBranchMembers218 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers218 6 4
  · have he : planeBranchMembers218.erase 6=planeBranchMembers194 := by decide
    rw [he]
    exact planeBranchBound194
  · have he : planeBranchMembers218.filter (encodedEdge 6)=planeBranchMembers217 := by decide
    rw [he]
    exact planeBranchBound217
end EntropyDesigns.QuadraticRefinement
