

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  rcases hx with hxA | hxB
  · -- Case: x ∈ A
    have hx_closure : x ∈ closure (interior A) := hA hxA
    have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
      have h_int_subset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact closure_mono h_int_subset
    exact h_subset hx_closure
  · -- Case: x ∈ B
    have hx_closure : x ∈ closure (interior B) := hB hxB
    have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
      have h_int_subset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact closure_mono h_int_subset
    exact h_subset hx_closure