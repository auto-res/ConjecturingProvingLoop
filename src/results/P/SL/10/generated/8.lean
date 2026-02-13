

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_clA : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : A ⊆ A ∪ B))
      exact h_subset hx_clA
  | inr hxB =>
      have hx_clB : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : B ⊆ A ∪ B))
      exact h_subset hx_clB