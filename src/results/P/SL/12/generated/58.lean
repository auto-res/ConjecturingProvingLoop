

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (closure A)) := by
  -- `interior A` is contained in `interior (closure A)` by monotonicity of `interior`.
  have h : (interior (A : Set X)) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Taking closures of both sides yields the desired inclusion.
  exact closure_mono h