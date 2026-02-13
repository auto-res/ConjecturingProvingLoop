

theorem Topology.isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen (A : Set X)) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx_closure
  have h_eq :
      closure (interior (closure (A : Set X))) = closure (A : Set X) :=
    Topology.closure_interior_closure_eq_closure_of_isOpen
      (X := X) (A := A) hA_open
  simpa [h_eq] using hx_closure