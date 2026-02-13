

theorem Topology.isOpen_closure_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure A) := by
  intro hDense
  -- From the density of `interior A`, we know `closure A` satisfies `P3`.
  have hP3 : Topology.P3 (closure A) :=
    Topology.closure_has_P3_of_denseInterior (X := X) (A := A) hDense
  -- For closed sets, `P3` is equivalent to being open.
  exact
    ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1) hP3