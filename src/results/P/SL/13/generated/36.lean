

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (X:=X) A) (hB : Topology.P3 (X:=X) B) :
    Topology.P3 (X:=X) (A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure A) := hA hxA
      have h_subset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have h_interior_subset :
          interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_interior_subset hx_intA
  | inr hxB =>
      have hx_intB : x ∈ interior (closure B) := hB hxB
      have h_subset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_interior_subset :
          interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_interior_subset hx_intB