

theorem closureInteriorClosure_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_open : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  -- From the openness of `A`, we obtain `P1 (closure A)`.
  have hP1 : Topology.P1 (closure A) :=
    Topology.isOpen_imp_P1_closure (X := X) (A := A) h_open
  -- Translate `P1 (closure A)` into the desired equality.
  exact
    (Topology.P1_closure_iff_closureInterior_eq_closure (X := X) (A := A)).1 hP1