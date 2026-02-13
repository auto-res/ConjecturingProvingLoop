

theorem Topology.P3_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = A) : Topology.P3 A := by
  -- The hypothesis yields the openness of `A`.
  have hOpen : IsOpen (A : Set X) := by
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [h] using this
  -- Every open set satisfies `P3`.
  exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen).2