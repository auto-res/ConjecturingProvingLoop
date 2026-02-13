

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      have h_subset : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_int_subset : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        have h_closure_subset :
            closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        have h_int_subset : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        have h_closure_subset :
            closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hx'