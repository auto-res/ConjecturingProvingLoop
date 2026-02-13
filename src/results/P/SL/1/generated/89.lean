

theorem Topology.P3_union_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → B ⊆ interior (closure A) → Topology.P3 (A ∪ B) := by
  intros hA hB
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- Points coming from `A` are handled by `hA`.
      have hxInt : x ∈ interior (closure A) := hA hxA
      -- Monotonicity of `interior` and `closure` upgrades the membership.
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hxInt
  | inr hxB =>
      -- Points coming from `B` are in `interior (closure A)` by assumption.
      have hxInt : x ∈ interior (closure A) := hB hxB
      -- As above, upgrade the membership.
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          exact Set.subset_union_left
        exact this
      exact hsubset hxInt