

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hx_closureA
  | inr hxB =>
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      have hSub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_right
      exact hSub hx_closureB