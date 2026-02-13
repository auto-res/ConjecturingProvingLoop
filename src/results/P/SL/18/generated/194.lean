

theorem P1_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (A : Set X)))) := by
  -- `interior (closure A)` is open.
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- Apply the existing lemma for the closure of an open set.
  exact
    Topology.P1_closure_of_open
      (A := interior (closure (A : Set X))) hOpen