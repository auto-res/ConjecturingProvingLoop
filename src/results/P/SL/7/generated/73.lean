

theorem Topology.P3_closure_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure (A : Set X) := by
  have hEquiv := (Topology.P3_closure_iff_isOpen (A := A))
  constructor
  · intro hP3
    have hOpen : IsOpen (closure (A : Set X)) := (hEquiv).1 hP3
    simpa using hOpen.interior_eq
  · intro hIntEq
    have hOpen : IsOpen (closure (A : Set X)) := by
      have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
      simpa [hIntEq] using this
    exact (hEquiv).2 hOpen