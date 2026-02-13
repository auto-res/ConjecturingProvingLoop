

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  unfold Topology.P1 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ closure (interior A) := hA hxA
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left)
      have hclosure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hx₁
  | inr hxB =>
      have hx₁ : x ∈ closure (interior B) := hB hxB
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right)
      have hclosure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hx₁