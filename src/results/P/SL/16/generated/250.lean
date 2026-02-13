

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, regard `x` as an element of `closure (interior A)`.
  have hx' : x ∈ closure (interior A) := interior_subset hx
  -- Use the existing inclusion on closures to conclude.
  have h_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure
      (X := X) (A := A)
  exact h_subset hx'