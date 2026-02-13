

theorem Topology.P1_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → (B ⊆ closure (interior A)) → Topology.P1 (A ∪ B) := by
  intro hP1A hBsubset
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_clA : x ∈ closure (interior A) := hP1A hxA
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hx_clA
  | inr hxB =>
      have hx_clA : x ∈ closure (interior A) := hBsubset hxB
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hx_clA