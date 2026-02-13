

theorem P2_closed_iff_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ IsClopen (A : Set X) := by
  -- For a closed set, `P2` is equivalent to openness.
  have hP2_open : Topology.P2 A ↔ IsOpen (A : Set X) :=
    Topology.P2_closed_iff_open (A := A) hA_closed
  -- Openness is equivalent to being clopen when closedness is already given.
  have hOpen_clopen : IsOpen (A : Set X) ↔ IsClopen (A : Set X) := by
    constructor
    · intro hOpen
      exact ⟨hA_closed, hOpen⟩
    · intro hClopen
      exact hClopen.2
  exact hP2_open.trans hOpen_clopen