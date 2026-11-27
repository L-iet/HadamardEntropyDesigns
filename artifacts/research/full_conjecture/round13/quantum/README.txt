Round13 flat real quantum measurements

quantum.tex is an input-ready fragment; paper.tex builds the standalone
PDF. It proves exact flat rankone POVM rigidity: commuting iff Hadamard,
projectivity deficit n-n^2*C, exact commutator energy, uniform tightframe
almost-commutation bounds, and absence of exact tensor activation.

The earlier character family supplies POVMs with effects almost
projective/commuting and exact flat Walsh Naimark dilations with vanishing
relative overhead, yet TV distance to every flat real projective mixture
tends to1. The comparison uses common outcomes labeled by actual sign
directions; unrestricted relabeling/noise/postprocessing/complex PVMs
are not obstructed. Relevant primary quantum simulation literature
Kotowski-Oszmaniec arXiv2501.09339 is cited and distinguished.

Run python check.py. Standard-library exact arithmetic verifies actual
matrix commutators for an 8-effect POVM and the compressed h16,k12 frame,
its tightness, exact orthogonality graph, all commutator bounds and full
flat Walsh dilation columns. checks.json has exact rational values.
No external code, Lean or commits. New code Apache-2.0 under parent
research LICENSE. No novelty or unknown-order existence assertion.
