/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original finite certificate; acceptance requires a successful recorded kernel check. -/
module
public import EntropyQuadraticClassification.PlaneBranch1
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def planeBranchMembers64 : Finset ℕ := ([1642,1708,2662,2668,2730,3178,3238,3244] : List ℕ).toFinset
theorem planeBranchBound64 : ListCliqueBound encodedEdge planeBranchMembers64 3 := by
  apply cliqueBound_coloring planeBranchMembers64 3 (fun x => match x with | 1642 => 0 | 1708 => 0 | 2662 => 1 | 2668 => 0 | 2730 => 0 | 3178 => 1 | 3238 => 1 | 3244 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers65 : Finset ℕ := ([192,1642,1708,1734,1740,2662,2668,2730,2762,3072,3178,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound65 : ListCliqueBound encodedEdge planeBranchMembers65 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers65 192 3
  · have he : planeBranchMembers65.erase 192=planeBranchMembers63 := by decide
    rw [he]
    exact planeBranchBound63
  · have he : planeBranchMembers65.filter (encodedEdge 192)=planeBranchMembers64 := by decide
    rw [he]
    exact planeBranchBound64
def planeBranchMembers66 : Finset ℕ := ([1642,1734,2662,2730,2762,3178,3238,3270] : List ℕ).toFinset
theorem planeBranchBound66 : ListCliqueBound encodedEdge planeBranchMembers66 3 := by
  apply cliqueBound_coloring planeBranchMembers66 3 (fun x => match x with | 1642 => 0 | 1734 => 0 | 2662 => 0 | 2730 => 1 | 2762 => 0 | 3178 => 1 | 3238 => 1 | 3270 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers67 : Finset ℕ := ([12,192,1642,1708,1734,1740,2662,2668,2730,2762,3072,3178,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound67 : ListCliqueBound encodedEdge planeBranchMembers67 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers67 12 3
  · have he : planeBranchMembers67.erase 12=planeBranchMembers65 := by decide
    rw [he]
    exact planeBranchBound65
  · have he : planeBranchMembers67.filter (encodedEdge 12)=planeBranchMembers66 := by decide
    rw [he]
    exact planeBranchBound66
def planeBranchMembers68 : Finset ℕ := ([12,192,1708,1734,2668,2762,3072,3178,3238,3276] : List ℕ).toFinset
theorem planeBranchBound68 : ListCliqueBound encodedEdge planeBranchMembers68 3 := by
  apply cliqueBound_coloring planeBranchMembers68 3 (fun x => match x with | 12 => 0 | 192 => 0 | 1708 => 1 | 1734 => 1 | 2668 => 2 | 2762 => 2 | 3072 => 0 | 3178 => 2 | 3238 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers69 : Finset ℕ := ([12,192,1642,1702,1708,1734,1740,2662,2668,2730,2762,3072,3178,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound69 : ListCliqueBound encodedEdge planeBranchMembers69 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers69 1702 3
  · have he : planeBranchMembers69.erase 1702=planeBranchMembers67 := by decide
    rw [he]
    exact planeBranchBound67
  · have he : planeBranchMembers69.filter (encodedEdge 1702)=planeBranchMembers68 := by decide
    rw [he]
    exact planeBranchBound68
def planeBranchMembers70 : Finset ℕ := ([12,192,1642,1644,1702,1708,1734,1738,1740,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound70 : ListCliqueBound encodedEdge planeBranchMembers70 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers70 2666 4
  · have he : planeBranchMembers70.erase 2666=planeBranchMembers60 := by decide
    rw [he]
    exact planeBranchBound60
  · have he : planeBranchMembers70.filter (encodedEdge 2666)=planeBranchMembers69 := by decide
    rw [he]
    exact planeBranchBound69
def planeBranchMembers71 : Finset ℕ := ([1708,1738,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound71 : ListCliqueBound encodedEdge planeBranchMembers71 4 := by
  apply cliqueBound_coloring planeBranchMembers71 4 (fun x => match x with | 1708 => 0 | 1738 => 0 | 3072 => 1 | 3174 => 1 | 3178 => 2 | 3180 => 3 | 3238 => 2 | 3242 => 0 | 3244 => 1 | 3270 => 3 | 3274 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers72 : Finset ℕ := ([1738,3072,3178,3180,3242,3244,3270] : List ℕ).toFinset
theorem planeBranchBound72 : ListCliqueBound encodedEdge planeBranchMembers72 3 := by
  apply cliqueBound_coloring planeBranchMembers72 3 (fun x => match x with | 1738 => 0 | 3072 => 1 | 3178 => 0 | 3180 => 1 | 3242 => 1 | 3244 => 2 | 3270 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers73 : Finset ℕ := ([1708,1734,1738,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound73 : ListCliqueBound encodedEdge planeBranchMembers73 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers73 1734 3
  · have he : planeBranchMembers73.erase 1734=planeBranchMembers71 := by decide
    rw [he]
    exact planeBranchBound71
  · have he : planeBranchMembers73.filter (encodedEdge 1734)=planeBranchMembers72 := by decide
    rw [he]
    exact planeBranchBound72
def planeBranchMembers74 : Finset ℕ := ([1708,3072,3180,3238,3242,3270,3274] : List ℕ).toFinset
theorem planeBranchBound74 : ListCliqueBound encodedEdge planeBranchMembers74 3 := by
  apply cliqueBound_coloring planeBranchMembers74 3 (fun x => match x with | 1708 => 0 | 3072 => 1 | 3180 => 0 | 3238 => 0 | 3242 => 1 | 3270 => 1 | 3274 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers75 : Finset ℕ := ([1644,1708,1734,1738,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound75 : ListCliqueBound encodedEdge planeBranchMembers75 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers75 1644 3
  · have he : planeBranchMembers75.erase 1644=planeBranchMembers73 := by decide
    rw [he]
    exact planeBranchBound73
  · have he : planeBranchMembers75.filter (encodedEdge 1644)=planeBranchMembers74 := by decide
    rw [he]
    exact planeBranchBound74
def planeBranchMembers76 : Finset ℕ := ([1708,1734,3072,3178,3180,3238,3274,3276] : List ℕ).toFinset
theorem planeBranchBound76 : ListCliqueBound encodedEdge planeBranchMembers76 3 := by
  apply cliqueBound_coloring planeBranchMembers76 3 (fun x => match x with | 1708 => 0 | 1734 => 0 | 3072 => 1 | 3178 => 1 | 3180 => 2 | 3238 => 0 | 3274 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers77 : Finset ℕ := ([1644,1702,1708,1734,1738,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound77 : ListCliqueBound encodedEdge planeBranchMembers77 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers77 1702 3
  · have he : planeBranchMembers77.erase 1702=planeBranchMembers75 := by decide
    rw [he]
    exact planeBranchBound75
  · have he : planeBranchMembers77.filter (encodedEdge 1702)=planeBranchMembers76 := by decide
    rw [he]
    exact planeBranchBound76
def planeBranchMembers78 : Finset ℕ := ([1644,1738,3072,3178,3238,3244,3270,3276] : List ℕ).toFinset
theorem planeBranchBound78 : ListCliqueBound encodedEdge planeBranchMembers78 3 := by
  apply cliqueBound_coloring planeBranchMembers78 3 (fun x => match x with | 1644 => 0 | 1738 => 0 | 3072 => 1 | 3178 => 0 | 3238 => 1 | 3244 => 2 | 3270 => 2 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers79 : Finset ℕ := ([1642,1644,1702,1708,1734,1738,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound79 : ListCliqueBound encodedEdge planeBranchMembers79 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers79 1642 3
  · have he : planeBranchMembers79.erase 1642=planeBranchMembers77 := by decide
    rw [he]
    exact planeBranchBound77
  · have he : planeBranchMembers79.filter (encodedEdge 1642)=planeBranchMembers78 := by decide
    rw [he]
    exact planeBranchBound78
def planeBranchMembers80 : Finset ℕ := ([1644,1708,1734,1738,3072,3174,3178,3238,3242,3276] : List ℕ).toFinset
theorem planeBranchBound80 : ListCliqueBound encodedEdge planeBranchMembers80 3 := by
  apply cliqueBound_coloring planeBranchMembers80 3 (fun x => match x with | 1644 => 0 | 1708 => 1 | 1734 => 0 | 1738 => 1 | 3072 => 2 | 3174 => 0 | 3178 => 2 | 3238 => 2 | 3242 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers81 : Finset ℕ := ([1642,1644,1702,1708,1734,1738,1740,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound81 : ListCliqueBound encodedEdge planeBranchMembers81 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers81 1740 3
  · have he : planeBranchMembers81.erase 1740=planeBranchMembers79 := by decide
    rw [he]
    exact planeBranchBound79
  · have he : planeBranchMembers81.filter (encodedEdge 1740)=planeBranchMembers80 := by decide
    rw [he]
    exact planeBranchBound80
def planeBranchMembers82 : Finset ℕ := ([12,192,1642,1644,1702,1708,1734,1738,1740,2560,2662,2666,2668,2726,2730,2732,2758,2762,2764,3072,3174,3178,3180,3238,3242,3244,3270,3274,3276] : List ℕ).toFinset
theorem planeBranchBound82 : ListCliqueBound encodedEdge planeBranchMembers82 5 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers82 2560 4
  · have he : planeBranchMembers82.erase 2560=planeBranchMembers70 := by decide
    rw [he]
    exact planeBranchBound70
  · have he : planeBranchMembers82.filter (encodedEdge 2560)=planeBranchMembers81 := by decide
    rw [he]
    exact planeBranchBound81
def planeBranchMembers83 : Finset ℕ := ([1642,1702,1708,1738,2668,2730,2758,2764,3072,3174,3180,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound83 : ListCliqueBound encodedEdge planeBranchMembers83 4 := by
  apply cliqueBound_coloring planeBranchMembers83 4 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1708 => 1 | 1738 => 1 | 2668 => 2 | 2730 => 0 | 2758 => 2 | 2764 => 1 | 3072 => 3 | 3174 => 2 | 3180 => 3 | 3242 => 3 | 3270 => 3 | 3276 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers84 : Finset ℕ := ([1642,1702,1708,2668,2730,3174,3242] : List ℕ).toFinset
theorem planeBranchBound84 : ListCliqueBound encodedEdge planeBranchMembers84 3 := by
  apply cliqueBound_coloring planeBranchMembers84 3 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1708 => 1 | 2668 => 1 | 2730 => 0 | 3174 => 2 | 3242 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers85 : Finset ℕ := ([1702,2668,2730,3174] : List ℕ).toFinset
theorem planeBranchBound85 : ListCliqueBound encodedEdge planeBranchMembers85 2 := by
  apply cliqueBound_coloring planeBranchMembers85 2 (fun x => match x with | 1702 => 0 | 2668 => 1 | 2730 => 0 | 3174 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers86 : Finset ℕ := ([1642,1702,1708,2668,2730,3174,3180,3242] : List ℕ).toFinset
theorem planeBranchBound86 : ListCliqueBound encodedEdge planeBranchMembers86 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers86 3180 2
  · have he : planeBranchMembers86.erase 3180=planeBranchMembers84 := by decide
    rw [he]
    exact planeBranchBound84
  · have he : planeBranchMembers86.filter (encodedEdge 3180)=planeBranchMembers85 := by decide
    rw [he]
    exact planeBranchBound85
def planeBranchMembers87 : Finset ℕ := ([192,1642,1702,1708,1738,2668,2730,2758,2764,3072,3174,3180,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound87 : ListCliqueBound encodedEdge planeBranchMembers87 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers87 192 3
  · have he : planeBranchMembers87.erase 192=planeBranchMembers83 := by decide
    rw [he]
    exact planeBranchBound83
  · have he : planeBranchMembers87.filter (encodedEdge 192)=planeBranchMembers86 := by decide
    rw [he]
    exact planeBranchBound86
def planeBranchMembers88 : Finset ℕ := ([1642,1702,1738,2730,2758,3174,3242] : List ℕ).toFinset
theorem planeBranchBound88 : ListCliqueBound encodedEdge planeBranchMembers88 3 := by
  apply cliqueBound_coloring planeBranchMembers88 3 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1738 => 1 | 2730 => 0 | 2758 => 1 | 3174 => 2 | 3242 => 2 | _ => 0)
  · decide
  · decide
def planeBranchMembers89 : Finset ℕ := ([1642,2730,2758,3174] : List ℕ).toFinset
theorem planeBranchBound89 : ListCliqueBound encodedEdge planeBranchMembers89 2 := by
  apply cliqueBound_coloring planeBranchMembers89 2 (fun x => match x with | 1642 => 0 | 2730 => 0 | 2758 => 1 | 3174 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers90 : Finset ℕ := ([1642,1702,1738,2730,2758,3174,3242,3270] : List ℕ).toFinset
theorem planeBranchBound90 : ListCliqueBound encodedEdge planeBranchMembers90 3 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers90 3270 2
  · have he : planeBranchMembers90.erase 3270=planeBranchMembers88 := by decide
    rw [he]
    exact planeBranchBound88
  · have he : planeBranchMembers90.filter (encodedEdge 3270)=planeBranchMembers89 := by decide
    rw [he]
    exact planeBranchBound89
def planeBranchMembers91 : Finset ℕ := ([12,192,1642,1702,1708,1738,2668,2730,2758,2764,3072,3174,3180,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound91 : ListCliqueBound encodedEdge planeBranchMembers91 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers91 12 3
  · have he : planeBranchMembers91.erase 12=planeBranchMembers87 := by decide
    rw [he]
    exact planeBranchBound87
  · have he : planeBranchMembers91.filter (encodedEdge 12)=planeBranchMembers90 := by decide
    rw [he]
    exact planeBranchBound90
def planeBranchMembers92 : Finset ℕ := ([12,192,1708,1738,2668,2758,3072,3174,3242,3276] : List ℕ).toFinset
theorem planeBranchBound92 : ListCliqueBound encodedEdge planeBranchMembers92 3 := by
  apply cliqueBound_coloring planeBranchMembers92 3 (fun x => match x with | 12 => 0 | 192 => 0 | 1708 => 1 | 1738 => 1 | 2668 => 2 | 2758 => 2 | 3072 => 0 | 3174 => 2 | 3242 => 1 | 3276 => 0 | _ => 0)
  · decide
  · decide
def planeBranchMembers93 : Finset ℕ := ([12,192,1642,1702,1708,1738,2662,2668,2730,2758,2764,3072,3174,3180,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound93 : ListCliqueBound encodedEdge planeBranchMembers93 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers93 2662 3
  · have he : planeBranchMembers93.erase 2662=planeBranchMembers91 := by decide
    rw [he]
    exact planeBranchBound91
  · have he : planeBranchMembers93.filter (encodedEdge 2662)=planeBranchMembers92 := by decide
    rw [he]
    exact planeBranchBound92
def planeBranchMembers94 : Finset ℕ := ([1642,1702,1708,1738,3072,3174,3180,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound94 : ListCliqueBound encodedEdge planeBranchMembers94 3 := by
  apply cliqueBound_coloring planeBranchMembers94 3 (fun x => match x with | 1642 => 0 | 1702 => 0 | 1708 => 1 | 1738 => 1 | 3072 => 2 | 3174 => 0 | 3180 => 2 | 3242 => 0 | 3270 => 2 | 3276 => 1 | _ => 0)
  · decide
  · decide
def planeBranchMembers95 : Finset ℕ := ([12,192,1642,1702,1708,1738,2560,2662,2668,2730,2758,2764,3072,3174,3180,3242,3270,3276] : List ℕ).toFinset
theorem planeBranchBound95 : ListCliqueBound encodedEdge planeBranchMembers95 4 := by
  apply cliqueBound_vertex_branch (fun h => encodedEdge_symm h) planeBranchMembers95 2560 3
  · have he : planeBranchMembers95.erase 2560=planeBranchMembers93 := by decide
    rw [he]
    exact planeBranchBound93
  · have he : planeBranchMembers95.filter (encodedEdge 2560)=planeBranchMembers94 := by decide
    rw [he]
    exact planeBranchBound94
end EntropyDesigns.QuadraticRefinement
