

theorem interior_closure_interior_closure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  -- Left‐to‐right inclusion.
  have h₁ :
      interior (closure (interior (closure (A : Set X)))) ⊆
        interior (closure (A : Set X)) := by
    -- Apply the existing monotonicity lemma to `A := closure A`.
    simpa [closure_closure] using
      (Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (A : Set X)))
  -- Right‐to‐left inclusion.
  have h₂ :
      interior (closure (A : Set X)) ⊆
        interior (closure (interior (closure (A : Set X)))) :=
    Topology.interior_closure_subset_interior_closure_interior_closure
      (X := X) (A := A)
  exact Set.Subset.antisymm h₁ h₂