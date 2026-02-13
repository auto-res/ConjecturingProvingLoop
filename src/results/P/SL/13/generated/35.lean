

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- Use P1 for A
      have hx_clA : x ∈ closure (interior A) := hA hxA
      -- Monotonicity of interior and closure under union
      have h_subset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have h_cl_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_cl_subset hx_clA
  | inr hxB =>
      -- Use P1 for B
      have hx_clB : x ∈ closure (interior B) := hB hxB
      have h_subset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_cl_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_cl_subset hx_clB