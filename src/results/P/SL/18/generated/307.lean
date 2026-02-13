

theorem P1_open_diff_closed {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU_open : IsOpen (U : Set X)) (hV_closed : IsClosed (V : Set X)) :
    Topology.P1 (U \ V) := by
  -- `U \ V` is open as the difference of an open set and a closed set.
  have hOpenDiff : IsOpen (U \ V : Set X) := IsOpen.diff hU_open hV_closed
  -- An open set satisfies property `P1`.
  exact Topology.P1_of_open hOpenDiff