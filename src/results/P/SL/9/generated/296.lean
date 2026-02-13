

theorem Topology.closureInterior_union_interiorClosure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ interior (closure A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl h_closureInt =>
      exact (Topology.closureInterior_subset_closure (A := A)) h_closureInt
  | inr h_interiorCl =>
      exact (Topology.interiorClosure_subset_closure (A := A)) h_interiorCl