

theorem P3_closure_imp_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (closure A)) :
    interior (closure A) = closure A := by
  -- `P3 (closure A)` implies that `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    Topology.P3_closure_isOpen_closure (X := X) (A := A) hP3
  -- For an open set, its interior is itself.
  simpa using hOpen.interior_eq