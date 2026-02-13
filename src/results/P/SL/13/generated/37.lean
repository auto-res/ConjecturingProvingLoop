

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      have h_int_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_subset
      exact h_int_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      have h_int_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_subset
      exact h_int_subset hxB'