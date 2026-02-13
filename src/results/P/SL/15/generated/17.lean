

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl h₁ =>
      have hxA : x ∈ interior (closure A) := hA h₁
      have h_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have : closure A ⊆ closure (A ∪ B) := closure_mono (Set.subset_union_left)
        exact interior_mono this
      exact h_mono hxA
  | inr h₂ =>
      have hxB : x ∈ interior (closure B) := hB h₂
      have h_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have : closure B ⊆ closure (A ∪ B) := closure_mono (Set.subset_union_right)
        exact interior_mono this
      exact h_mono hxB