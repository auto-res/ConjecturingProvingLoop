

theorem Topology.boundary_eq_empty_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] (A : Set X) :
    closure (A : Set X) \ interior A = (∅ : Set X) := by
  have hClosed : IsClosed (A : Set X) := isClosed_discrete _
  have hOpen   : IsOpen   (A : Set X) := isOpen_discrete _
  simpa using Topology.boundary_eq_empty_of_isClopen (A := A) hClosed hOpen