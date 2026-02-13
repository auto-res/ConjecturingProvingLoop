

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, use `interior_subset` to move from the interior to the closure.
  have hx₁ : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx
  -- Then, apply the monotonicity lemma already proved for closures of interiors.
  have hSub :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  exact hSub hx₁