

theorem P1_union_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → (B : Set X) ⊆ closure (interior A) → Topology.P1 (A ∪ B) := by
  intro hP1 hB
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  -- `closure (interior A)` is contained in the target set via monotonicity.
  have hMono :
      closure (interior (A : Set X)) ⊆
        closure (interior (A ∪ B : Set X)) := by
    apply closure_mono
    exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Dispatch the two union cases.
  cases hx with
  | inl hxA =>
      have : x ∈ closure (interior (A : Set X)) := hP1 hxA
      exact hMono this
  | inr hxB =>
      have : x ∈ closure (interior (A : Set X)) := hB hxB
      exact hMono this