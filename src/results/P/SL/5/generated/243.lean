

theorem P1_union_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : (B : Set X) ⊆ closure (interior A)) :
    Topology.P1 (X := X) (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`.
  have h_mono :
      closure (interior A : Set X) ⊆
        closure (interior (A ∪ B : Set X)) := by
    have h_inner :
        (interior A : Set X) ⊆ interior (A ∪ B) :=
      interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
    exact closure_mono h_inner
  cases hx with
  | inl hxA =>
      -- Case `x ∈ A`.
      exact h_mono (hA hxA)
  | inr hxB =>
      -- Case `x ∈ B`.
      exact h_mono (hB hxB)