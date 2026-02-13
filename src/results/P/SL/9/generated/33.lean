

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) :
    Topology.P3 (A := A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hxIntA : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure A ⊆ closure (A ∪ B) := by
          have hA_subset : (A : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact closure_mono hA_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntA
  | inr hxB =>
      have hxIntB : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure B ⊆ closure (A ∪ B) := by
          have hB_subset : (B : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          exact closure_mono hB_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntB