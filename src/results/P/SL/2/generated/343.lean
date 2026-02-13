

theorem Topology.isOpen_of_interior_closure_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) = A → IsOpen A := by
  intro hEq
  have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa [hEq] using this