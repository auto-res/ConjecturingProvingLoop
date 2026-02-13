

theorem denseInterior_implies_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure (interior A)) := by
  intro hDense
  -- `closure (interior A)` is open, thanks to the density of `interior A`.
  have hOpen : IsOpen (closure (interior A)) :=
    isOpen_closure_interior_of_denseInterior (X := X) (A := A) hDense
  -- Open sets satisfy `P3`.
  exact Topology.isOpen_implies_P3
    (X := X) (A := closure (interior A)) hOpen