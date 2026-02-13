

theorem closure_interior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- `P2` gives `closure A = closure (interior A)`.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hP2
  -- We establish the two inclusions separately.
  apply le_antisymm
  · -- Always, `closure (interior (closure A)) ⊆ closure A`.
    exact
      Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  · -- `closure A ⊆ closure (interior (closure A))`, using the equality above.
    have h_subset :
        closure (interior A) ⊆ closure (interior (closure (A : Set X))) :=
      Topology.closure_interior_subset_closure_interior_closure (X := X) (A := A)
    simpa [h_eq] using h_subset