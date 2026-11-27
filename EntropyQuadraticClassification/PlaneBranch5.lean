/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.PlaneBranch4
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def planeBranchMembers160 : Finset ℕ := ([2668,2732,2758,2762,3072,3174,3178,3238,3242,3276] : List ℕ).toFinset
theorem planeBranchBound160 : ListCliqueBound encodedEdge planeBranchMembers160 3 := by
  apply cliqueBound_coloring planeBranchMembers160 3 (fun x => match x with | 2668 => 0 | 2732 => 1 | 2758 => 0 | 2762 => 1 | 3072 => 2 | 3174 => 0 | 3178 => 2 | 3238 => 2 | 3242 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers161 : Finset ℕ := ([2666,2668,2726,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound161 : ListCliqueBound encodedEdge planeBranchMembers161 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers161 2764 3
  · have he : planeBranchMembers161.erase 2764=planeBranchMembers159 := by decide
    rw [he]
    exact planeBranchBound159
  · have he : planeBranchMembers161.filter (encodedEdge 2764)=planeBranchMembers160 := by decide
    rw [he]
    exact planeBranchBound160
def planeBranchMembers162 : Finset ℕ := ([2666,2726,2732,2762,3072,3174,3180,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound162 : ListCliqueBound encodedEdge planeBranchMembers162 3 := by
  apply cliqueBound_coloring planeBranchMembers162 3 (fun x => match x with | 2666 => 0 | 2726 => 0 | 2732 => 1 | 2762 => 1 | 3072 => 2 | 3174 => 0 | 3180 => 2 | 3242 => 0 | 3270 => 2 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers163 : Finset ℕ := ([2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound163 : ListCliqueBound encodedEdge planeBranchMembers163 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers163 2730 3
  · have he : planeBranchMembers163.erase 2730=planeBranchMembers161 := by decide
    rw [he]
    exact planeBranchBound161
  · have he : planeBranchMembers163.filter (encodedEdge 2730)=planeBranchMembers162 := by decide
    rw [he]
    exact planeBranchBound162
def planeBranchMembers164 : Finset ℕ := ([2666,2668,2726,2758,3072,3174,3242,3244,3274,3276] : List ℕ).toFinset
theorem planeBranchBound164 : ListCliqueBound encodedEdge planeBranchMembers164 3 := by
  apply cliqueBound_coloring planeBranchMembers164 3 (fun x => match x with | 2666 => 0 | 2668 => 1 | 2726 => 0 | 2758 => 1 | 3072 => 2 | 3174 => 0 | 3242 => 0 | 3244 => 2 | 3274 => 2 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers165 : Finset ℕ := ([2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound165 : ListCliqueBound encodedEdge planeBranchMembers165 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers165 2662 3
  · have he : planeBranchMembers165.erase 2662=planeBranchMembers163 := by decide
    rw [he]
    exact planeBranchBound163
  · have he : planeBranchMembers165.filter (encodedEdge 2662)=planeBranchMembers164 := by decide
    rw [he]
    exact planeBranchBound164
def planeBranchMembers166 : Finset ℕ := ([3072,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound166 : ListCliqueBound encodedEdge planeBranchMembers166 3 := by
  apply cliqueBound_coloring planeBranchMembers166 3 (fun x => match x with | 3072 => 0 | 3178 => 0 | 3180 => 1 | 3238 => 0 | 3242 => 1 | 3244 => 2 | 3270 => 1 | 3274 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers167 : Finset ℕ := ([3178,3180,3238,3270] : List ℕ).toFinset
theorem planeBranchBound167 : ListCliqueBound encodedEdge planeBranchMembers167 2 := by
  apply cliqueBound_coloring planeBranchMembers167 2 (fun x => match x with | 3178 => 0 | 3180 => 1 | 3238 => 0 | 3270 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers168 : Finset ℕ := ([3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound168 : ListCliqueBound encodedEdge planeBranchMembers168 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers168 3174 2
  · have he : planeBranchMembers168.erase 3174=planeBranchMembers166 := by decide
    rw [he]
    exact planeBranchBound166
  · have he : planeBranchMembers168.filter (encodedEdge 3174)=planeBranchMembers167 := by decide
    rw [he]
    exact planeBranchBound167
def planeBranchMembers169 : Finset ℕ := ([2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound169 : ListCliqueBound encodedEdge planeBranchMembers169 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers169 2560 3
  · have he : planeBranchMembers169.erase 2560=planeBranchMembers165 := by decide
    rw [he]
    exact planeBranchBound165
  · have he : planeBranchMembers169.filter (encodedEdge 2560)=planeBranchMembers168 := by decide
    rw [he]
    exact planeBranchBound168
def planeBranchMembers170 : Finset ℕ := ([10,12,160,192,1536,1638,1642,1644,1702,1706,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound170 : ListCliqueBound encodedEdge planeBranchMembers170 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers170 1536 4
  · have he : planeBranchMembers170.erase 1536=planeBranchMembers150 := by decide
    rw [he]
    exact planeBranchBound150
  · have he : planeBranchMembers170.filter (encodedEdge 1536)=planeBranchMembers169 := by decide
    rw [he]
    exact planeBranchBound169
def planeBranchMembers171 : Finset ℕ := ([192,1708,1734,1738,2726,2758,2762,2764,3238,3242,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound171 : ListCliqueBound encodedEdge planeBranchMembers171 4 := by
  apply cliqueBound_coloring planeBranchMembers171 4 (fun x => match x with | 192 => 0 | 1708 => 1 | 1734 => 0 | 1738 => 1 | 2726 => 2 | 2758 => 3 | 2762 => 0 | 2764 => 1 | 3238 => 3 | 3242 => 2 | 3270 => 2 | 3274 => 3 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers172 : Finset ℕ := ([192,1708,1734,1738,2726,2764,3270,3274] : List ℕ).toFinset
theorem planeBranchBound172 : ListCliqueBound encodedEdge planeBranchMembers172 3 := by
  apply cliqueBound_coloring planeBranchMembers172 3 (fun x => match x with | 192 => 0 | 1708 => 1 | 1734 => 0 | 1738 => 1 | 2726 => 2 | 2764 => 0 | 3270 => 2 | 3274 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers173 : Finset ℕ := ([192,1708,1734,1738,2726,2732,2758,2762,2764,3238,3242,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound173 : ListCliqueBound encodedEdge planeBranchMembers173 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers173 2732 3
  · have he : planeBranchMembers173.erase 2732=planeBranchMembers171 := by decide
    rw [he]
    exact planeBranchBound171
  · have he : planeBranchMembers173.filter (encodedEdge 2732)=planeBranchMembers172 := by decide
    rw [he]
    exact planeBranchBound172
def planeBranchMembers174 : Finset ℕ := ([1708,1734,1738,2726,2764,3238,3242,3276] : List ℕ).toFinset
theorem planeBranchBound174 : ListCliqueBound encodedEdge planeBranchMembers174 3 := by
  apply cliqueBound_coloring planeBranchMembers174 3 (fun x => match x with | 1708 => 0 | 1734 => 0 | 1738 => 1 | 2726 => 0 | 2764 => 0 | 3238 => 2 | 3242 => 1 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers175 : Finset ℕ := ([192,1708,1734,1738,1740,2726,2732,2758,2762,2764,3238,3242,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound175 : ListCliqueBound encodedEdge planeBranchMembers175 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers175 1740 3
  · have he : planeBranchMembers175.erase 1740=planeBranchMembers173 := by decide
    rw [he]
    exact planeBranchBound173
  · have he : planeBranchMembers175.filter (encodedEdge 1740)=planeBranchMembers174 := by decide
    rw [he]
    exact planeBranchBound174
def planeBranchMembers176 : Finset ℕ := ([192,1708,1738,2758,2764,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound176 : ListCliqueBound encodedEdge planeBranchMembers176 3 := by
  apply cliqueBound_coloring planeBranchMembers176 3 (fun x => match x with | 192 => 0 | 1708 => 1 | 1738 => 0 | 2758 => 0 | 2764 => 1 | 3242 => 2 | 3270 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers177 : Finset ℕ := ([192,1706,1708,1734,1738,1740,2726,2732,2758,2762,2764,3238,3242,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound177 : ListCliqueBound encodedEdge planeBranchMembers177 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers177 1706 3
  · have he : planeBranchMembers177.erase 1706=planeBranchMembers175 := by decide
    rw [he]
    exact planeBranchBound175
  · have he : planeBranchMembers177.filter (encodedEdge 1706)=planeBranchMembers176 := by decide
    rw [he]
    exact planeBranchBound176
def planeBranchMembers178 : Finset ℕ := ([192,1708,1734,1738,2732,2758,2762,3238,3242,3276] : List ℕ).toFinset
theorem planeBranchBound178 : ListCliqueBound encodedEdge planeBranchMembers178 3 := by
  apply cliqueBound_coloring planeBranchMembers178 3 (fun x => match x with | 192 => 0 | 1708 => 1 | 1734 => 0 | 1738 => 1 | 2732 => 2 | 2758 => 2 | 2762 => 0 | 3238 => 2 | 3242 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers179 : Finset ℕ := ([192,1706,1708,1734,1738,1740,2726,2732,2758,2762,2764,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound179 : ListCliqueBound encodedEdge planeBranchMembers179 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers179 3244 3
  · have he : planeBranchMembers179.erase 3244=planeBranchMembers177 := by decide
    rw [he]
    exact planeBranchBound177
  · have he : planeBranchMembers179.filter (encodedEdge 3244)=planeBranchMembers178 := by decide
    rw [he]
    exact planeBranchBound178
def planeBranchMembers180 : Finset ℕ := ([192,1706,1734,1740,2726,2732,2762,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound180 : ListCliqueBound encodedEdge planeBranchMembers180 3 := by
  apply cliqueBound_coloring planeBranchMembers180 3 (fun x => match x with | 192 => 0 | 1706 => 1 | 1734 => 0 | 1740 => 1 | 2726 => 2 | 2732 => 1 | 2762 => 0 | 3242 => 2 | 3270 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers181 : Finset ℕ := ([192,1706,1708,1734,1738,1740,2726,2730,2732,2758,2762,2764,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound181 : ListCliqueBound encodedEdge planeBranchMembers181 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers181 2730 3
  · have he : planeBranchMembers181.erase 2730=planeBranchMembers179 := by decide
    rw [he]
    exact planeBranchBound179
  · have he : planeBranchMembers181.filter (encodedEdge 2730)=planeBranchMembers180 := by decide
    rw [he]
    exact planeBranchBound180
def planeBranchMembers182 : Finset ℕ := ([1706,1708,1734,2726,2764,3238,3274] : List ℕ).toFinset
theorem planeBranchBound182 : ListCliqueBound encodedEdge planeBranchMembers182 3 := by
  apply cliqueBound_coloring planeBranchMembers182 3 (fun x => match x with | 1706 => 0 | 1708 => 1 | 1734 => 0 | 2726 => 0 | 2764 => 1 | 3238 => 2 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers183 : Finset ℕ := ([1706,2726,2764,3274] : List ℕ).toFinset
theorem planeBranchBound183 : ListCliqueBound encodedEdge planeBranchMembers183 2 := by
  apply cliqueBound_coloring planeBranchMembers183 2 (fun x => match x with | 1706 => 0 | 2726 => 0 | 2764 => 1 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers184 : Finset ℕ := ([1706,1708,1734,2726,2764,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound184 : ListCliqueBound encodedEdge planeBranchMembers184 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers184 3276 2
  · have he : planeBranchMembers184.erase 3276=planeBranchMembers182 := by decide
    rw [he]
    exact planeBranchBound182
  · have he : planeBranchMembers184.filter (encodedEdge 3276)=planeBranchMembers183 := by decide
    rw [he]
    exact planeBranchBound183
def planeBranchMembers185 : Finset ℕ := ([1708,2764,3238,3274] : List ℕ).toFinset
theorem planeBranchBound185 : ListCliqueBound encodedEdge planeBranchMembers185 2 := by
  apply cliqueBound_coloring planeBranchMembers185 2 (fun x => match x with | 1708 => 0 | 2764 => 0 | 3238 => 1 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers186 : Finset ℕ := ([1706,1708,1734,2726,2762,2764,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound186 : ListCliqueBound encodedEdge planeBranchMembers186 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers186 2762 2
  · have he : planeBranchMembers186.erase 2762=planeBranchMembers184 := by decide
    rw [he]
    exact planeBranchBound184
  · have he : planeBranchMembers186.filter (encodedEdge 2762)=planeBranchMembers185 := by decide
    rw [he]
    exact planeBranchBound185
def planeBranchMembers187 : Finset ℕ := ([1706,1708,2726,3238] : List ℕ).toFinset
theorem planeBranchBound187 : ListCliqueBound encodedEdge planeBranchMembers187 2 := by
  apply cliqueBound_coloring planeBranchMembers187 2 (fun x => match x with | 1706 => 0 | 1708 => 1 | 2726 => 0 | 3238 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers188 : Finset ℕ := ([192,1706,1708,1734,2726,2762,2764,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound188 : ListCliqueBound encodedEdge planeBranchMembers188 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers188 192 2
  · have he : planeBranchMembers188.erase 192=planeBranchMembers186 := by decide
    rw [he]
    exact planeBranchBound186
  · have he : planeBranchMembers188.filter (encodedEdge 192)=planeBranchMembers187 := by decide
    rw [he]
    exact planeBranchBound187
def planeBranchMembers189 : Finset ℕ := ([192,1702,1706,1708,1734,1738,1740,2726,2730,2732,2758,2762,2764,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound189 : ListCliqueBound encodedEdge planeBranchMembers189 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers189 1702 3
  · have he : planeBranchMembers189.erase 1702=planeBranchMembers181 := by decide
    rw [he]
    exact planeBranchBound181
  · have he : planeBranchMembers189.filter (encodedEdge 1702)=planeBranchMembers188 := by decide
    rw [he]
    exact planeBranchBound188
def planeBranchMembers190 : Finset ℕ := ([192,1738,1740,2758,2762,2764,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound190 : ListCliqueBound encodedEdge planeBranchMembers190 3 := by
  apply cliqueBound_coloring planeBranchMembers190 3 (fun x => match x with | 192 => 0 | 1738 => 0 | 1740 => 1 | 2758 => 0 | 2762 => 1 | 2764 => 2 | 3270 => 1 | 3274 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers191 : Finset ℕ := ([1738,1740,2758,3270] : List ℕ).toFinset
theorem planeBranchBound191 : ListCliqueBound encodedEdge planeBranchMembers191 2 := by
  apply cliqueBound_coloring planeBranchMembers191 2 (fun x => match x with | 1738 => 0 | 1740 => 1 | 2758 => 0 | 3270 => 1 | _ => 0)
  · decide
  · decide
end EntropyDesigns.QuadraticRefinement
