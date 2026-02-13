

theorem isOpen_closure_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    IsOpen (closure A) := by
  -- From the density of the interior we obtain `P3 (closure A)`.
  have hP3 : Topology.P3 (closure A) :=
    denseInterior_imp_P3_closure (X := X) (A := A) h_dense
  -- A set satisfying `P3` and being closed is open.
  exact P3_closure_isOpen_closure (X := X) (A := A) hP3