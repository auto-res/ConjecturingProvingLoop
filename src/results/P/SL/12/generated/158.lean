

theorem Topology.interior_closure_union_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hx_int =>
      -- `x ∈ interior (closure A)` and this set is contained in `closure A`.
      have h_sub : interior (closure (A : Set X)) ⊆ closure A :=
        interior_subset
      exact h_sub hx_int
  | inr hx_cl =>
      -- `x ∈ closure (interior A)` and this set is contained in `closure A`.
      have h_sub : closure (interior (A : Set X)) ⊆ closure A :=
        Topology.closure_interior_subset_closure (X := X) (A := A)
      exact h_sub hx_cl