

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ interior (closure (interior A)) := hA hxA
      have hSub : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hx₁
  | inr hxB =>
      have hx₁ : x ∈ interior (closure (interior B)) := hB hxB
      have hSub : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact hSub hx₁