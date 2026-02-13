

theorem P123_open_diff_closed {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    Topology.P1 (U \ V) ∧ Topology.P2 (U \ V) ∧ Topology.P3 (U \ V) := by
  -- The difference of an open set and a closed set is open.
  have hOpenDiff : IsOpen (U \ V : Set X) := IsOpen.diff hU_open hV_closed
  -- Apply the combined `P123` result for open sets.
  exact Topology.P123_of_open hOpenDiff