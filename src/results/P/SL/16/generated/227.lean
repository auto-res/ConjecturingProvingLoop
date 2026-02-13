

theorem Topology.interior_closure_eq_self_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) → interior (closure A) = closure A := by
  intro hP2
  -- `P2` for `closure A` is equivalent to `IsOpen (closure A)`.
  have hOpen : IsOpen (closure A) :=
    (Topology.P2_closure_iff_open_closure (X := X) (A := A)).1 hP2
  -- For an open set, its interior equals itself.
  exact
    (Topology.isOpen_closure_iff_interior_eq_self (X := X) (A := A)).1 hOpen