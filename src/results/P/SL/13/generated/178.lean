

theorem Topology.interior_closure_interior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `A ⊆ A ∪ B`
      have h_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure : closure (interior (A : Set X)) ⊆
          closure (interior (A ∪ B)) :=
        closure_mono h_subset
      -- Apply monotonicity of `interior`.
      exact (interior_mono h_closure) hA
  | inr hB =>
      -- `B ⊆ A ∪ B`
      have h_subset : interior (B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure : closure (interior (B : Set X)) ⊆
          closure (interior (A ∪ B)) :=
        closure_mono h_subset
      -- Apply monotonicity of `interior`.
      exact (interior_mono h_closure) hB