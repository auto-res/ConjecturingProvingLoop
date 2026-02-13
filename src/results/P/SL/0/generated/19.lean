

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_in : x ∈ interior (closure A) := hA hxA
      have hMono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have : closure A ⊆ closure (A ∪ B) := by
          simpa using closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact hMono hx_in
  | inr hxB =>
      -- `x` comes from `B`
      have hx_in : x ∈ interior (closure B) := hB hxB
      have hMono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have : closure B ⊆ closure (A ∪ B) := by
          simpa using closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact hMono hx_in