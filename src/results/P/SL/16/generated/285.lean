

theorem Topology.P3_of_interior_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure A) = closure A) :
    Topology.P3 (X := X) A := by
  -- From the equality we obtain that `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    (Topology.isOpen_closure_iff_interior_eq_self (X := X) (A := A)).mpr h
  -- An open closure of `A` implies `P3 A`.
  exact Topology.P3_of_open_closure (X := X) (A := A) hOpen