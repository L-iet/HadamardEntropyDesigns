/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.PlaneBranch0
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def planeBranchMembers32 : Finset ℕ := ([1708,2662,2730,3178,3180,3238] : List ℕ).toFinset
theorem planeBranchBound32 : ListCliqueBound encodedEdge planeBranchMembers32 3 := by
  apply cliqueBound_coloring planeBranchMembers32 3 (fun x => match x with | 1708 => 0 | 2662 => 1 | 2730 => 0 | 3178 => 1 | 3180 => 2 | 3238 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers33 : Finset ℕ := ([1642,1702,1708,2662,2668,2730,3174,3178,3180,3238,3242,3244] : List ℕ).toFinset
theorem planeBranchBound33 : ListCliqueBound encodedEdge planeBranchMembers33 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers33 3174 3
  · have he : planeBranchMembers33.erase 3174=planeBranchMembers31 := by decide
    rw [he]
    exact planeBranchBound31
  · have he : planeBranchMembers33.filter (encodedEdge 3174)=planeBranchMembers32 := by decide
    rw [he]
    exact planeBranchBound32
def planeBranchMembers34 : Finset ℕ := ([1642,1708,2668,2730,3174,3178,3244] : List ℕ).toFinset
theorem planeBranchBound34 : ListCliqueBound encodedEdge planeBranchMembers34 3 := by
  apply cliqueBound_coloring planeBranchMembers34 3 (fun x => match x with | 1642 => 0 | 1708 => 0 | 2668 => 0 | 2730 => 0 | 3174 => 1 | 3178 => 2 | 3244 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers35 : Finset ℕ := ([1642,1702,1708,2662,2668,2730,2732,3174,3178,3180,3238,3242,3244] : List ℕ).toFinset
theorem planeBranchBound35 : ListCliqueBound encodedEdge planeBranchMembers35 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers35 2732 3
  · have he : planeBranchMembers35.erase 2732=planeBranchMembers33 := by decide
    rw [he]
    exact planeBranchBound33
  · have he : planeBranchMembers35.filter (encodedEdge 2732)=planeBranchMembers34 := by decide
    rw [he]
    exact planeBranchBound34
def planeBranchMembers36 : Finset ℕ := ([1642,1708,2668,2730,3180,3238,3242] : List ℕ).toFinset
theorem planeBranchBound36 : ListCliqueBound encodedEdge planeBranchMembers36 3 := by
  apply cliqueBound_coloring planeBranchMembers36 3 (fun x => match x with | 1642 => 0 | 1708 => 0 | 2668 => 0 | 2730 => 0 | 3180 => 1 | 3238 => 1 | 3242 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers37 : Finset ℕ := ([1642,1644,1702,1708,2662,2668,2730,2732,3174,3178,3180,3238,3242,3244] : List ℕ).toFinset
theorem planeBranchBound37 : ListCliqueBound encodedEdge planeBranchMembers37 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers37 1644 3
  · have he : planeBranchMembers37.erase 1644=planeBranchMembers35 := by decide
    rw [he]
    exact planeBranchBound35
  · have he : planeBranchMembers37.filter (encodedEdge 1644)=planeBranchMembers36 := by decide
    rw [he]
    exact planeBranchBound36
def planeBranchMembers38 : Finset ℕ := ([192,1642,1644,1702,1708,1734,1738,1740,2662,2668,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound38 : ListCliqueBound encodedEdge planeBranchMembers38 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers38 192 4
  · have he : planeBranchMembers38.erase 192=planeBranchMembers26 := by decide
    rw [he]
    exact planeBranchBound26
  · have he : planeBranchMembers38.filter (encodedEdge 192)=planeBranchMembers37 := by decide
    rw [he]
    exact planeBranchBound37
def planeBranchMembers39 : Finset ℕ := ([1702,1738,2662,2730,2758,3178,3238,3270,3274] : List ℕ).toFinset
theorem planeBranchBound39 : ListCliqueBound encodedEdge planeBranchMembers39 4 := by
  apply cliqueBound_coloring planeBranchMembers39 4 (fun x => match x with | 1702 => 0 | 1738 => 0 | 2662 => 1 | 2730 => 0 | 2758 => 0 | 3178 => 1 | 3238 => 1 | 3270 => 2 | 3274 => 3 | _ => 0)
  · decide
  · decide
def planeBranchMembers40 : Finset ℕ := ([1738,2758,3178,3238,3270] : List ℕ).toFinset
theorem planeBranchBound40 : ListCliqueBound encodedEdge planeBranchMembers40 3 := by
  apply cliqueBound_coloring planeBranchMembers40 3 (fun x => match x with | 1738 => 0 | 2758 => 0 | 3178 => 1 | 3238 => 1 | 3270 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers41 : Finset ℕ := ([1642,1702,1738,2662,2730,2758,3178,3238,3270,3274] : List ℕ).toFinset
theorem planeBranchBound41 : ListCliqueBound encodedEdge planeBranchMembers41 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers41 1642 3
  · have he : planeBranchMembers41.erase 1642=planeBranchMembers39 := by decide
    rw [he]
    exact planeBranchBound39
  · have he : planeBranchMembers41.filter (encodedEdge 1642)=planeBranchMembers40 := by decide
    rw [he]
    exact planeBranchBound40
def planeBranchMembers42 : Finset ℕ := ([2662,2730,2758,3178,3238,3274] : List ℕ).toFinset
theorem planeBranchBound42 : ListCliqueBound encodedEdge planeBranchMembers42 3 := by
  apply cliqueBound_coloring planeBranchMembers42 3 (fun x => match x with | 2662 => 0 | 2730 => 0 | 2758 => 1 | 3178 => 0 | 3238 => 0 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers43 : Finset ℕ := ([1642,1702,1738,2662,2730,2758,3178,3238,3242,3270,3274] : List ℕ).toFinset
theorem planeBranchBound43 : ListCliqueBound encodedEdge planeBranchMembers43 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers43 3242 3
  · have he : planeBranchMembers43.erase 3242=planeBranchMembers41 := by decide
    rw [he]
    exact planeBranchBound41
  · have he : planeBranchMembers43.filter (encodedEdge 3242)=planeBranchMembers42 := by decide
    rw [he]
    exact planeBranchBound42
def planeBranchMembers44 : Finset ℕ := ([1738,2662,2730,3178,3238,3270] : List ℕ).toFinset
theorem planeBranchBound44 : ListCliqueBound encodedEdge planeBranchMembers44 3 := by
  apply cliqueBound_coloring planeBranchMembers44 3 (fun x => match x with | 1738 => 0 | 2662 => 1 | 2730 => 0 | 3178 => 0 | 3238 => 1 | 3270 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers45 : Finset ℕ := ([1642,1702,1738,2662,2730,2758,3174,3178,3238,3242,3270,3274] : List ℕ).toFinset
theorem planeBranchBound45 : ListCliqueBound encodedEdge planeBranchMembers45 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers45 3174 3
  · have he : planeBranchMembers45.erase 3174=planeBranchMembers43 := by decide
    rw [he]
    exact planeBranchBound43
  · have he : planeBranchMembers45.filter (encodedEdge 3174)=planeBranchMembers44 := by decide
    rw [he]
    exact planeBranchBound44
def planeBranchMembers46 : Finset ℕ := ([1702,1738,2730,2758,3174,3238,3274] : List ℕ).toFinset
theorem planeBranchBound46 : ListCliqueBound encodedEdge planeBranchMembers46 3 := by
  apply cliqueBound_coloring planeBranchMembers46 3 (fun x => match x with | 1702 => 0 | 1738 => 0 | 2730 => 0 | 2758 => 0 | 3174 => 1 | 3238 => 2 | 3274 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers47 : Finset ℕ := ([1642,1702,1738,2662,2730,2758,2762,3174,3178,3238,3242,3270,3274] : List ℕ).toFinset
theorem planeBranchBound47 : ListCliqueBound encodedEdge planeBranchMembers47 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers47 2762 3
  · have he : planeBranchMembers47.erase 2762=planeBranchMembers45 := by decide
    rw [he]
    exact planeBranchBound45
  · have he : planeBranchMembers47.filter (encodedEdge 2762)=planeBranchMembers46 := by decide
    rw [he]
    exact planeBranchBound46
def planeBranchMembers48 : Finset ℕ := ([1702,1738,2730,2758,3178,3242,3270] : List ℕ).toFinset
theorem planeBranchBound48 : ListCliqueBound encodedEdge planeBranchMembers48 3 := by
  apply cliqueBound_coloring planeBranchMembers48 3 (fun x => match x with | 1702 => 0 | 1738 => 0 | 2730 => 0 | 2758 => 0 | 3178 => 1 | 3242 => 2 | 3270 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers49 : Finset ℕ := ([1642,1702,1734,1738,2662,2730,2758,2762,3174,3178,3238,3242,3270,3274] : List ℕ).toFinset
theorem planeBranchBound49 : ListCliqueBound encodedEdge planeBranchMembers49 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers49 1734 3
  · have he : planeBranchMembers49.erase 1734=planeBranchMembers47 := by decide
    rw [he]
    exact planeBranchBound47
  · have he : planeBranchMembers49.filter (encodedEdge 1734)=planeBranchMembers48 := by decide
    rw [he]
    exact planeBranchBound48
def planeBranchMembers50 : Finset ℕ := ([12,192,1642,1644,1702,1708,1734,1738,1740,2662,2668,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound50 : ListCliqueBound encodedEdge planeBranchMembers50 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers50 12 4
  · have he : planeBranchMembers50.erase 12=planeBranchMembers38 := by decide
    rw [he]
    exact planeBranchBound38
  · have he : planeBranchMembers50.filter (encodedEdge 12)=planeBranchMembers49 := by decide
    rw [he]
    exact planeBranchBound49
def planeBranchMembers51 : Finset ℕ := ([1644,1702,1738,2662,2730,2732,2758,3072,3178,3180,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound51 : ListCliqueBound encodedEdge planeBranchMembers51 4 := by
  apply cliqueBound_coloring planeBranchMembers51 4 (fun x => match x with | 1644 => 0 | 1702 => 0 | 1738 => 0 | 2662 => 1 | 2730 => 1 | 2732 => 2 | 2758 => 2 | 3072 => 3 | 3178 => 1 | 3180 => 3 | 3238 => 1 | 3274 => 3 | 3276 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers52 : Finset ℕ := ([1644,1738,2662,2730,3072,3178,3238,3276] : List ℕ).toFinset
theorem planeBranchBound52 : ListCliqueBound encodedEdge planeBranchMembers52 3 := by
  apply cliqueBound_coloring planeBranchMembers52 3 (fun x => match x with | 1644 => 0 | 1738 => 0 | 2662 => 1 | 2730 => 1 | 3072 => 2 | 3178 => 0 | 3238 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers53 : Finset ℕ := ([1644,1702,1738,1740,2662,2730,2732,2758,3072,3178,3180,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound53 : ListCliqueBound encodedEdge planeBranchMembers53 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers53 1740 3
  · have he : planeBranchMembers53.erase 1740=planeBranchMembers51 := by decide
    rw [he]
    exact planeBranchBound51
  · have he : planeBranchMembers53.filter (encodedEdge 1740)=planeBranchMembers52 := by decide
    rw [he]
    exact planeBranchBound52
def planeBranchMembers54 : Finset ℕ := ([1644,1702,2662,2730,2732,3178,3180,3238] : List ℕ).toFinset
theorem planeBranchBound54 : ListCliqueBound encodedEdge planeBranchMembers54 3 := by
  apply cliqueBound_coloring planeBranchMembers54 3 (fun x => match x with | 1644 => 0 | 1702 => 0 | 2662 => 0 | 2730 => 1 | 2732 => 0 | 3178 => 1 | 3180 => 2 | 3238 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers55 : Finset ℕ := ([192,1644,1702,1738,1740,2662,2730,2732,2758,3072,3178,3180,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound55 : ListCliqueBound encodedEdge planeBranchMembers55 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers55 192 3
  · have he : planeBranchMembers55.erase 192=planeBranchMembers53 := by decide
    rw [he]
    exact planeBranchBound53
  · have he : planeBranchMembers55.filter (encodedEdge 192)=planeBranchMembers54 := by decide
    rw [he]
    exact planeBranchBound54
def planeBranchMembers56 : Finset ℕ := ([1702,1738,2662,2730,2758,3178,3238,3274] : List ℕ).toFinset
theorem planeBranchBound56 : ListCliqueBound encodedEdge planeBranchMembers56 3 := by
  apply cliqueBound_coloring planeBranchMembers56 3 (fun x => match x with | 1702 => 0 | 1738 => 0 | 2662 => 1 | 2730 => 0 | 2758 => 0 | 3178 => 1 | 3238 => 1 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers57 : Finset ℕ := ([12,192,1644,1702,1738,1740,2662,2730,2732,2758,3072,3178,3180,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound57 : ListCliqueBound encodedEdge planeBranchMembers57 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers57 12 3
  · have he : planeBranchMembers57.erase 12=planeBranchMembers55 := by decide
    rw [he]
    exact planeBranchBound55
  · have he : planeBranchMembers57.filter (encodedEdge 12)=planeBranchMembers56 := by decide
    rw [he]
    exact planeBranchBound56
def planeBranchMembers58 : Finset ℕ := ([12,192,1644,1738,2732,2758,3072,3178,3238,3276] : List ℕ).toFinset
theorem planeBranchBound58 : ListCliqueBound encodedEdge planeBranchMembers58 3 := by
  apply cliqueBound_coloring planeBranchMembers58 3 (fun x => match x with | 12 => 0 | 192 => 0 | 1644 => 1 | 1738 => 1 | 2732 => 2 | 2758 => 2 | 3072 => 0 | 3178 => 1 | 3238 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers59 : Finset ℕ := ([12,192,1642,1644,1702,1738,1740,2662,2730,2732,2758,3072,3178,3180,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound59 : ListCliqueBound encodedEdge planeBranchMembers59 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers59 1642 3
  · have he : planeBranchMembers59.erase 1642=planeBranchMembers57 := by decide
    rw [he]
    exact planeBranchBound57
  · have he : planeBranchMembers59.filter (encodedEdge 1642)=planeBranchMembers58 := by decide
    rw [he]
    exact planeBranchBound58
def planeBranchMembers60 : Finset ℕ := ([12,192,1642,1644,1702,1708,1734,1738,1740,2662,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound60 : ListCliqueBound encodedEdge planeBranchMembers60 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers60 2726 4
  · have he : planeBranchMembers60.erase 2726=planeBranchMembers50 := by decide
    rw [he]
    exact planeBranchBound50
  · have he : planeBranchMembers60.filter (encodedEdge 2726)=planeBranchMembers59 := by decide
    rw [he]
    exact planeBranchBound59
def planeBranchMembers61 : Finset ℕ := ([1642,1708,1734,2662,2668,2730,2762,3072,3178,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound61 : ListCliqueBound encodedEdge planeBranchMembers61 4 := by
  apply cliqueBound_coloring planeBranchMembers61 4 (fun x => match x with | 1642 => 0 | 1708 => 0 | 1734 => 0 | 2662 => 1 | 2668 => 2 | 2730 => 1 | 2762 => 2 | 3072 => 3 | 3178 => 1 | 3238 => 1 | 3244 => 3 | 3270 => 3 | 3276 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers62 : Finset ℕ := ([1708,1734,2662,2730,3072,3178,3238,3276] : List ℕ).toFinset
theorem planeBranchBound62 : ListCliqueBound encodedEdge planeBranchMembers62 3 := by
  apply cliqueBound_coloring planeBranchMembers62 3 (fun x => match x with | 1708 => 0 | 1734 => 0 | 2662 => 1 | 2730 => 1 | 3072 => 2 | 3178 => 1 | 3238 => 0 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers63 : Finset ℕ := ([1642,1708,1734,1740,2662,2668,2730,2762,3072,3178,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound63 : ListCliqueBound encodedEdge planeBranchMembers63 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers63 1740 3
  · have he : planeBranchMembers63.erase 1740=planeBranchMembers61 := by decide
    rw [he]
    exact planeBranchBound61
  · have he : planeBranchMembers63.filter (encodedEdge 1740)=planeBranchMembers62 := by decide
    rw [he]
    exact planeBranchBound62
end EntropyDesigns.QuadraticRefinement
