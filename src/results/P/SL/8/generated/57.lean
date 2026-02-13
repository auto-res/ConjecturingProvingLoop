

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' := hA hxA
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      have hxB' := hB hxB
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB'