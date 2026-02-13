

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure A) := hA hxA
      have h_sub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        exact interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_sub hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure B) := hB hxB
      have h_sub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        exact interior_mono (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_sub hx_int