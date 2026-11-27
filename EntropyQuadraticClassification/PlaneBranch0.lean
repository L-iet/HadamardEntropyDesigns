/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.EncodedParityGraph
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def planeBranchMembers0 : Finset ℕ := ([1642,1702,1740,2662,2730,2732,2762,3178,3180,3238,3244,3270,3274] : List ℕ).toFinset
theorem planeBranchBound0 : ListCliqueBound encodedEdge planeBranchMembers0 5 := by
  apply cliqueBound_coloring planeBranchMembers0 5 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1740 => 0 | 2662 => 1 | 2730 => 1 | 2732 => 2 | 2762 => 2 | 3178 => 1 | 3180 => 3 | 3238 => 1 | 3244 => 4 | 3270 => 3 | 3274 => 4 | _ => 0)
  · decide
  · decide
def planeBranchMembers1 : Finset ℕ := ([1642,2662,2762,3178,3180,3244,3270] : List ℕ).toFinset
theorem planeBranchBound1 : ListCliqueBound encodedEdge planeBranchMembers1 4 := by
  apply cliqueBound_coloring planeBranchMembers1 4 (fun x => match x with | 1642 => 0 | 2662 => 0 | 2762 => 0 | 3178 => 1 | 3180 => 2 | 3244 => 1 | 3270 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers2 : Finset ℕ := ([1642,1702,1740,2662,2730,2732,2758,2762,3178,3180,3238,3244,3270,3274] : List ℕ).toFinset
theorem planeBranchBound2 : ListCliqueBound encodedEdge planeBranchMembers2 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers2 2758 4
  · have he : planeBranchMembers2.erase 2758=planeBranchMembers0 := by decide
    rw [he]
    exact planeBranchBound0
  · have he : planeBranchMembers2.filter (encodedEdge 2758)=planeBranchMembers1 := by decide
    rw [he]
    exact planeBranchBound1
def planeBranchMembers3 : Finset ℕ := ([1702,2662,2732,3180,3238,3270,3274] : List ℕ).toFinset
theorem planeBranchBound3 : ListCliqueBound encodedEdge planeBranchMembers3 4 := by
  apply cliqueBound_coloring planeBranchMembers3 4 (fun x => match x with | 1702 => 0 | 2662 => 0 | 2732 => 0 | 3180 => 1 | 3238 => 1 | 3270 => 2 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers4 : Finset ℕ := ([1642,1702,1740,2662,2668,2730,2732,2758,2762,3178,3180,3238,3244,3270,3274] : List ℕ).toFinset
theorem planeBranchBound4 : ListCliqueBound encodedEdge planeBranchMembers4 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers4 2668 4
  · have he : planeBranchMembers4.erase 2668=planeBranchMembers2 := by decide
    rw [he]
    exact planeBranchBound2
  · have he : planeBranchMembers4.filter (encodedEdge 2668)=planeBranchMembers3 := by decide
    rw [he]
    exact planeBranchBound3
def planeBranchMembers5 : Finset ℕ := ([1642,1702,1740,2662,2730,3180,3244,3270,3274] : List ℕ).toFinset
theorem planeBranchBound5 : ListCliqueBound encodedEdge planeBranchMembers5 4 := by
  apply cliqueBound_coloring planeBranchMembers5 4 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1740 => 0 | 2662 => 1 | 2730 => 1 | 3180 => 2 | 3244 => 3 | 3270 => 2 | 3274 => 3 | _ => 0)
  · decide
  · decide
def planeBranchMembers6 : Finset ℕ := ([1642,1702,1740,2662,2668,2730,2732,2758,2762,3178,3180,3238,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound6 : ListCliqueBound encodedEdge planeBranchMembers6 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers6 3276 4
  · have he : planeBranchMembers6.erase 3276=planeBranchMembers4 := by decide
    rw [he]
    exact planeBranchBound4
  · have he : planeBranchMembers6.filter (encodedEdge 3276)=planeBranchMembers5 := by decide
    rw [he]
    exact planeBranchBound5
def planeBranchMembers7 : Finset ℕ := ([1740,2662,2668,2730,2758,3178,3238,3244,3274] : List ℕ).toFinset
theorem planeBranchBound7 : ListCliqueBound encodedEdge planeBranchMembers7 4 := by
  apply cliqueBound_coloring planeBranchMembers7 4 (fun x => match x with | 1740 => 0 | 2662 => 1 | 2668 => 0 | 2730 => 1 | 2758 => 0 | 3178 => 1 | 3238 => 1 | 3244 => 2 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers8 : Finset ℕ := ([1642,1702,1740,2662,2668,2730,2732,2758,2762,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound8 : ListCliqueBound encodedEdge planeBranchMembers8 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers8 3242 4
  · have he : planeBranchMembers8.erase 3242=planeBranchMembers6 := by decide
    rw [he]
    exact planeBranchBound6
  · have he : planeBranchMembers8.filter (encodedEdge 3242)=planeBranchMembers7 := by decide
    rw [he]
    exact planeBranchBound7
def planeBranchMembers9 : Finset ℕ := ([1740,2662,2730,2732,2762,3178,3180,3238,3270] : List ℕ).toFinset
theorem planeBranchBound9 : ListCliqueBound encodedEdge planeBranchMembers9 4 := by
  apply cliqueBound_coloring planeBranchMembers9 4 (fun x => match x with | 1740 => 0 | 2662 => 1 | 2730 => 1 | 2732 => 0 | 2762 => 0 | 3178 => 1 | 3180 => 2 | 3238 => 1 | 3270 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers10 : Finset ℕ := ([1642,1702,1740,2662,2668,2730,2732,2758,2762,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound10 : ListCliqueBound encodedEdge planeBranchMembers10 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers10 3174 4
  · have he : planeBranchMembers10.erase 3174=planeBranchMembers8 := by decide
    rw [he]
    exact planeBranchBound8
  · have he : planeBranchMembers10.filter (encodedEdge 3174)=planeBranchMembers9 := by decide
    rw [he]
    exact planeBranchBound9
def planeBranchMembers11 : Finset ℕ := ([1642,1740,2662,2668,2732,2762,3174,3180,3238,3244,3274] : List ℕ).toFinset
theorem planeBranchBound11 : ListCliqueBound encodedEdge planeBranchMembers11 4 := by
  apply cliqueBound_coloring planeBranchMembers11 4 (fun x => match x with | 1642 => 0 | 1740 => 0 | 2662 => 1 | 2668 => 0 | 2732 => 1 | 2762 => 0 | 3174 => 2 | 3180 => 1 | 3238 => 1 | 3244 => 2 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers12 : Finset ℕ := ([1642,1702,1738,1740,2662,2668,2730,2732,2758,2762,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound12 : ListCliqueBound encodedEdge planeBranchMembers12 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers12 1738 4
  · have he : planeBranchMembers12.erase 1738=planeBranchMembers10 := by decide
    rw [he]
    exact planeBranchBound10
  · have he : planeBranchMembers12.filter (encodedEdge 1738)=planeBranchMembers11 := by decide
    rw [he]
    exact planeBranchBound11
def planeBranchMembers13 : Finset ℕ := ([1702,1740,2662,2732,2758,2762,3174,3178,3244,3270,3274] : List ℕ).toFinset
theorem planeBranchBound13 : ListCliqueBound encodedEdge planeBranchMembers13 4 := by
  apply cliqueBound_coloring planeBranchMembers13 4 (fun x => match x with | 1702 => 0 | 1740 => 0 | 2662 => 1 | 2732 => 0 | 2758 => 0 | 2762 => 1 | 3174 => 2 | 3178 => 1 | 3244 => 2 | 3270 => 1 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers14 : Finset ℕ := ([1642,1702,1708,1738,1740,2662,2668,2730,2732,2758,2762,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound14 : ListCliqueBound encodedEdge planeBranchMembers14 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers14 1708 4
  · have he : planeBranchMembers14.erase 1708=planeBranchMembers12 := by decide
    rw [he]
    exact planeBranchBound12
  · have he : planeBranchMembers14.filter (encodedEdge 1708)=planeBranchMembers13 := by decide
    rw [he]
    exact planeBranchBound13
def planeBranchMembers15 : Finset ℕ := ([1642,1702,1740,2668,2732,2758,2762,3174,3178,3238,3242,3276] : List ℕ).toFinset
theorem planeBranchBound15 : ListCliqueBound encodedEdge planeBranchMembers15 4 := by
  apply cliqueBound_coloring planeBranchMembers15 4 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1740 => 0 | 2668 => 1 | 2732 => 2 | 2758 => 1 | 2762 => 2 | 3174 => 1 | 3178 => 3 | 3238 => 3 | 3242 => 2 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers16 : Finset ℕ := ([1642,1702,1708,1738,1740,2662,2668,2730,2732,2758,2762,2764,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound16 : ListCliqueBound encodedEdge planeBranchMembers16 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers16 2764 4
  · have he : planeBranchMembers16.erase 2764=planeBranchMembers14 := by decide
    rw [he]
    exact planeBranchBound14
  · have he : planeBranchMembers16.filter (encodedEdge 2764)=planeBranchMembers15 := by decide
    rw [he]
    exact planeBranchBound15
def planeBranchMembers17 : Finset ℕ := ([1702,1738,1740,2668,2730,2732,2758,3178,3180,3242,3244,3270] : List ℕ).toFinset
theorem planeBranchBound17 : ListCliqueBound encodedEdge planeBranchMembers17 4 := by
  apply cliqueBound_coloring planeBranchMembers17 4 (fun x => match x with | 1702 => 0 | 1738 => 0 | 1740 => 1 | 2668 => 1 | 2730 => 0 | 2732 => 2 | 2758 => 0 | 3178 => 3 | 3180 => 2 | 3242 => 2 | 3244 => 1 | 3270 => 3 | _ => 0)
  · decide
  · decide
def planeBranchMembers18 : Finset ℕ := ([1642,1702,1708,1734,1738,1740,2662,2668,2730,2732,2758,2762,2764,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound18 : ListCliqueBound encodedEdge planeBranchMembers18 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers18 1734 4
  · have he : planeBranchMembers18.erase 1734=planeBranchMembers16 := by decide
    rw [he]
    exact planeBranchBound16
  · have he : planeBranchMembers18.filter (encodedEdge 1734)=planeBranchMembers17 := by decide
    rw [he]
    exact planeBranchBound17
def planeBranchMembers19 : Finset ℕ := ([1642,1708,1740,2668,2730,2758,2762,3180,3238,3242,3270,3274] : List ℕ).toFinset
theorem planeBranchBound19 : ListCliqueBound encodedEdge planeBranchMembers19 4 := by
  apply cliqueBound_coloring planeBranchMembers19 4 (fun x => match x with | 1642 => 0 | 1708 => 0 | 1740 => 1 | 2668 => 0 | 2730 => 0 | 2758 => 1 | 2762 => 2 | 3180 => 3 | 3238 => 3 | 3242 => 2 | 3270 => 2 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers20 : Finset ℕ := ([1642,1644,1702,1708,1734,1738,1740,2662,2668,2730,2732,2758,2762,2764,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound20 : ListCliqueBound encodedEdge planeBranchMembers20 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers20 1644 4
  · have he : planeBranchMembers20.erase 1644=planeBranchMembers18 := by decide
    rw [he]
    exact planeBranchBound18
  · have he : planeBranchMembers20.filter (encodedEdge 1644)=planeBranchMembers19 := by decide
    rw [he]
    exact planeBranchBound19
def planeBranchMembers21 : Finset ℕ := ([1642,1702,1708,1738,1740,2662,2668,2730,2732,2758,2762,2764] : List ℕ).toFinset
theorem planeBranchBound21 : ListCliqueBound encodedEdge planeBranchMembers21 4 := by
  apply cliqueBound_coloring planeBranchMembers21 4 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1708 => 1 | 1738 => 1 | 1740 => 0 | 2662 => 2 | 2668 => 3 | 2730 => 1 | 2732 => 2 | 2758 => 3 | 2762 => 2 | 2764 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers22 : Finset ℕ := ([1702,1738,1740,2668,2730,2732,2758] : List ℕ).toFinset
theorem planeBranchBound22 : ListCliqueBound encodedEdge planeBranchMembers22 3 := by
  apply cliqueBound_coloring planeBranchMembers22 3 (fun x => match x with | 1702 => 0 | 1738 => 0 | 1740 => 1 | 2668 => 1 | 2730 => 0 | 2732 => 2 | 2758 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers23 : Finset ℕ := ([1642,1702,1708,1734,1738,1740,2662,2668,2730,2732,2758,2762,2764] : List ℕ).toFinset
theorem planeBranchBound23 : ListCliqueBound encodedEdge planeBranchMembers23 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers23 1734 3
  · have he : planeBranchMembers23.erase 1734=planeBranchMembers21 := by decide
    rw [he]
    exact planeBranchBound21
  · have he : planeBranchMembers23.filter (encodedEdge 1734)=planeBranchMembers22 := by decide
    rw [he]
    exact planeBranchBound22
def planeBranchMembers24 : Finset ℕ := ([1642,1708,1740,2668,2730,2758,2762] : List ℕ).toFinset
theorem planeBranchBound24 : ListCliqueBound encodedEdge planeBranchMembers24 3 := by
  apply cliqueBound_coloring planeBranchMembers24 3 (fun x => match x with | 1642 => 0 | 1708 => 0 | 1740 => 1 | 2668 => 0 | 2730 => 0 | 2758 => 1 | 2762 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers25 : Finset ℕ := ([1642,1644,1702,1708,1734,1738,1740,2662,2668,2730,2732,2758,2762,2764] : List ℕ).toFinset
theorem planeBranchBound25 : ListCliqueBound encodedEdge planeBranchMembers25 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers25 1644 3
  · have he : planeBranchMembers25.erase 1644=planeBranchMembers23 := by decide
    rw [he]
    exact planeBranchBound23
  · have he : planeBranchMembers25.filter (encodedEdge 1644)=planeBranchMembers24 := by decide
    rw [he]
    exact planeBranchBound24
def planeBranchMembers26 : Finset ℕ := ([1642,1644,1702,1708,1734,1738,1740,2662,2668,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound26 : ListCliqueBound encodedEdge planeBranchMembers26 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers26 3072 4
  · have he : planeBranchMembers26.erase 3072=planeBranchMembers20 := by decide
    rw [he]
    exact planeBranchBound20
  · have he : planeBranchMembers26.filter (encodedEdge 3072)=planeBranchMembers25 := by decide
    rw [he]
    exact planeBranchBound25
def planeBranchMembers27 : Finset ℕ := ([1642,1708,2662,2668,2730,3178,3180,3238,3244] : List ℕ).toFinset
theorem planeBranchBound27 : ListCliqueBound encodedEdge planeBranchMembers27 4 := by
  apply cliqueBound_coloring planeBranchMembers27 4 (fun x => match x with | 1642 => 0 | 1708 => 0 | 2662 => 1 | 2668 => 0 | 2730 => 0 | 3178 => 1 | 3180 => 2 | 3238 => 1 | 3244 => 3 | _ => 0)
  · decide
  · decide
def planeBranchMembers28 : Finset ℕ := ([1708,2668,3178,3180,3238] : List ℕ).toFinset
theorem planeBranchBound28 : ListCliqueBound encodedEdge planeBranchMembers28 3 := by
  apply cliqueBound_coloring planeBranchMembers28 3 (fun x => match x with | 1708 => 0 | 2668 => 0 | 3178 => 1 | 3180 => 2 | 3238 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers29 : Finset ℕ := ([1642,1702,1708,2662,2668,2730,3178,3180,3238,3244] : List ℕ).toFinset
theorem planeBranchBound29 : ListCliqueBound encodedEdge planeBranchMembers29 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers29 1702 3
  · have he : planeBranchMembers29.erase 1702=planeBranchMembers27 := by decide
    rw [he]
    exact planeBranchBound27
  · have he : planeBranchMembers29.filter (encodedEdge 1702)=planeBranchMembers28 := by decide
    rw [he]
    exact planeBranchBound28
def planeBranchMembers30 : Finset ℕ := ([2662,2668,2730,3178,3238,3244] : List ℕ).toFinset
theorem planeBranchBound30 : ListCliqueBound encodedEdge planeBranchMembers30 3 := by
  apply cliqueBound_coloring planeBranchMembers30 3 (fun x => match x with | 2662 => 0 | 2668 => 1 | 2730 => 0 | 3178 => 0 | 3238 => 0 | 3244 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers31 : Finset ℕ := ([1642,1702,1708,2662,2668,2730,3178,3180,3238,3242,3244] : List ℕ).toFinset
theorem planeBranchBound31 : ListCliqueBound encodedEdge planeBranchMembers31 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers31 3242 3
  · have he : planeBranchMembers31.erase 3242=planeBranchMembers29 := by decide
    rw [he]
    exact planeBranchBound29
  · have he : planeBranchMembers31.filter (encodedEdge 3242)=planeBranchMembers30 := by decide
    rw [he]
    exact planeBranchBound30
end EntropyDesigns.QuadraticRefinement
