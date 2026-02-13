

theorem P2_open_diff_closed {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    Topology.P2 (U \ V) := by
  -- `U \ V` is an open set because it is the difference of an open set and a closed set.
  have hOpenDiff : IsOpen (U \ V : Set X) := by
    simpa using (IsOpen.diff (α := X) hU_open hV_closed)
  -- Apply the lemma asserting `P2` for open sets.
  exact Topology.P2_of_open hOpenDiff