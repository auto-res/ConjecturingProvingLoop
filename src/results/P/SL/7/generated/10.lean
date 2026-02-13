

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure A) := hA hxA
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hx_intA
  | inr hxB =>
      have hx_intB : x ∈ interior (closure B) := hB hxB
      have hSub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_right
      exact hSub hx_intB