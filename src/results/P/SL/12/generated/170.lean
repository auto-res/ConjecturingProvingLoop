

theorem Topology.closure_interior_eq_univ_of_P1_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A)
    (h_dense : closure (A : Set X) = (Set.univ : Set X)) :
    closure (interior A) = (Set.univ : Set X) := by
  -- From `P1` we know the two closures coincide.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  -- Rewrite `h_dense` via `h_eq` to obtain the desired equality.
  calc
    closure (interior A) = closure (A : Set X) := by
      simpa using h_eq.symm
    _ = (Set.univ : Set X) := h_dense