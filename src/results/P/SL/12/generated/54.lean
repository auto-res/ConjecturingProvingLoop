

theorem Topology.interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `A` branch
      have h_sub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        -- `closure A ⊆ closure (A ∪ B)`
        have h_cl : (closure (A : Set X)) ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        -- Take interiors
        exact interior_mono h_cl
      exact h_sub hA
  | inr hB =>
      -- `B` branch
      have h_sub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        -- `closure B ⊆ closure (A ∪ B)`
        have h_cl : (closure (B : Set X)) ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        -- Take interiors
        exact interior_mono h_cl
      exact h_sub hB