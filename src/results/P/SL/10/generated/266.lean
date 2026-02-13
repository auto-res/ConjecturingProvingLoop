

theorem Topology.P2_interior_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P2 (interior (closure A) ∪ interior (closure B)) := by
  -- The union of two open sets is open.
  have h_open :
      IsOpen (interior (closure A) ∪ interior (closure B)) := by
    have hA : IsOpen (interior (closure A)) := isOpen_interior
    have hB : IsOpen (interior (closure B)) := isOpen_interior
    exact hA.union hB
  -- Open sets satisfy `P2`.
  exact
    Topology.isOpen_implies_P2
      (X := X)
      (A := interior (closure A) ∪ interior (closure B))
      h_open