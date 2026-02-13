

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- Use monotonicity with the inclusion `A ⊆ A ∪ B`.
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        Topology.interior_closure_interior_mono
          (X := X) (A := A) (B := A ∪ B) (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h_subset hA
  | inr hB =>
      -- Symmetric argument for the `B` component.
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        Topology.interior_closure_interior_mono
          (X := X) (A := B) (B := A ∪ B) (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h_subset hB