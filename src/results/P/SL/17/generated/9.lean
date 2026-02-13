

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  unfold Topology.P3 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ interior (closure A) := hA hxA
      have hsubset_closure : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx₁
  | inr hxB =>
      have hx₁ : x ∈ interior (closure B) := hB hxB
      have hsubset_closure : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx₁