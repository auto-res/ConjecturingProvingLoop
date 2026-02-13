

theorem Topology.interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Use monotonicity of `closure` to obtain the required inclusion.
      have h_closure_subset : closure A ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      -- Apply `interior_mono` to get the inclusion on interiors.
      have h_int_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_subset
      exact h_int_subset hxA
  | inr hxB =>
      have h_closure_subset : closure B ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      have h_int_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_subset
      exact h_int_subset hxB