

theorem Topology.closure_interior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A ⊆ interior (A ∪ B)`
      have h_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion
      have h_closure_subset :
          closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_closure_subset hxA
  | inr hxB =>
      -- `interior B ⊆ interior (A ∪ B)`
      have h_subset : interior (B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion
      have h_closure_subset :
          closure (interior (B : Set X)) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_closure_subset hxB