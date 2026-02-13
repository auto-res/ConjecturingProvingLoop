

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_subset hxB'