

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) :
    Topology.P1 (A := A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have h_subset' : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_subset'
        exact closure_mono h_int_subset
      exact h_subset hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : interior B ⊆ interior (A ∪ B) := by
          have h_subset' : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_subset'
        exact closure_mono h_int_subset
      exact h_subset hx_closure