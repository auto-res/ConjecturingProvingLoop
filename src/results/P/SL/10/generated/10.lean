

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure (interior A)) := hA hxA
      have h_subset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hx_int