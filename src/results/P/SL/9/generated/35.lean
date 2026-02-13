

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) :
    Topology.P2 (A := A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      -- Use `P2` on `A`
      have hxIntA : x ∈ interior (closure (interior A)) := hA hxA
      -- Show this interior is contained in the desired one
      have h_subset : interior (closure (interior A)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        -- Monotonicity of `interior` and `closure`
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact interior_mono h_sub
        have h_closure_subset : closure (interior A) ⊆
                                closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntA
  | inr hxB =>
      -- Symmetric case for `B`
      have hxIntB : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : interior (closure (interior B)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        have h_int_subset : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          exact interior_mono h_sub
        have h_closure_subset : closure (interior B) ⊆
                                closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntB