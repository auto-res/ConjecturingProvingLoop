

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure A ⊆ closure (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact closure_mono h_sub
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      have hxB' := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure B ⊆ closure (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact closure_mono h_sub
        exact interior_mono h_closure
      exact h_subset hxB'