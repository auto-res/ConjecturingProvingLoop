

theorem Topology.frontier_eq_empty_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    frontier (A : Set X) = (∅ : Set X) := by
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  have h_interior : interior (A : Set X) = A := hA_open.interior_eq
  simp [frontier, h_closure, h_interior, Set.diff_self]