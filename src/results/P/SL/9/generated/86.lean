

theorem Topology.closureInterior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A ⊆ interior (A ∪ B)`
      have h_int_subset : interior A ⊆ interior (A ∪ B) := by
        have h_subset : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono h_subset
      -- Taking closures preserves inclusions.
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxA
  | inr hxB =>
      -- Symmetric argument for `B`.
      have h_int_subset : interior B ⊆ interior (A ∪ B) := by
        have h_subset : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono h_subset
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxB