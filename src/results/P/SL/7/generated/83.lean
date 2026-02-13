

theorem Topology.P3_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → (B ⊆ interior (closure A)) → Topology.P3 (A ∪ B) := by
  intro hP3A hBsubset
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure A) := hP3A hxA
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hx_intA
  | inr hxB =>
      have hx_intA : x ∈ interior (closure A) := hBsubset hxB
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hx_intA