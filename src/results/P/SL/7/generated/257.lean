

theorem Topology.P3_of_interiorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = closure (A : Set X)) :
    Topology.P3 A := by
  -- The given equality shows that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [h] using this
  -- Apply the existing result that openness of `closure A` implies `P3 A`.
  exact Topology.P3_of_open_closure (A := A) hOpen