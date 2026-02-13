

theorem Topology.closureInterior_union_interiorClosure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ∪ interior (closure A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl h_closureInt =>
      -- `closure (interior A)` is contained in `closure A`
      have h_subset : closure (interior (A : Set X)) ⊆ closure A :=
        closure_mono (interior_subset : interior (A : Set X) ⊆ A)
      exact h_subset h_closureInt
  | inr h_interiorCl =>
      -- `interior (closure A)` is contained in `closure A`
      exact (interior_subset : interior (closure A) ⊆ closure A) h_interiorCl