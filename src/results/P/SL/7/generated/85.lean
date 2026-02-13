

theorem Topology.P2_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → (B ⊆ interior (closure (interior A))) → Topology.P2 (A ∪ B) := by
  intro hP2A hBsubset
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure (interior A)) := hP2A hxA
      have hSub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hx_intA
  | inr hxB =>
      have hx_intA : x ∈ interior (closure (interior A)) := hBsubset hxB
      have hSub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hx_intA