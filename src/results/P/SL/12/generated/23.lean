

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (A ∪ B) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  -- Deal with the two cases coming from the union
  cases hx with
  | inl hxA =>
      -- From `P1` for `A`
      have hx_cl : x ∈ closure (interior A) := hA hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have h_sub : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        exact closure_mono h_int
      exact h_sub hx_cl
  | inr hxB =>
      -- From `P1` for `B`
      have hx_cl : x ∈ closure (interior B) := hB hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have h_sub : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        exact closure_mono h_int
      exact h_sub hx_cl