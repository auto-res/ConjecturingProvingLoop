

theorem open_of_closed_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X))
    (hDenseInt : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    IsOpen (A : Set X) := by
  -- The density assumption yields `P3` for the closed set `A`.
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.dense_interior_satisfies_P3 (A := A) hDenseInt
  -- A closed set satisfying `P3` is necessarily open.
  exact (Topology.open_of_P3_closed (A := A) hClosed) hP3