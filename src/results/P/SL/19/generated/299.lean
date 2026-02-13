

theorem Topology.P2_of_frontier_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) → Topology.P2 (A := A) := by
  intro hFrontier
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.frontier_eq_empty_iff_isOpen_and_isClosed (A := A)).1 hFrontier).1
  exact Topology.P2_of_isOpen (A := A) hOpen