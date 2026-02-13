

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  unfold Topology.P2 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset_int : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hsubset_clos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      have hsubset : interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_clos
      exact hsubset hx₁
  | inr hxB =>
      have hx₁ : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset_int : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hsubset_clos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      have hsubset : interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_clos
      exact hsubset hx₁