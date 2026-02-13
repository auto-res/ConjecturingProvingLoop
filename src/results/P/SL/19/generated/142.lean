

theorem Topology.closure_interior_closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) ⊆ closure A := by
  -- First, rewrite the left-hand side using a previously proven equality.
  have hEq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) :=
    Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
      (X := X) (A := A)
  -- We already know `closure (interior (closure A)) ⊆ closure A`.
  have hSub :
      closure (interior (closure A)) ⊆ closure A :=
    Topology.closure_interior_closure_subset_closure (A := A)
  -- Assemble the inclusions.
  intro x hx
  have : x ∈ closure (interior (closure (interior (closure A)))) := hx
  have hx' : x ∈ closure (interior (closure A)) := by
    simpa [hEq] using this
  exact hSub hx'