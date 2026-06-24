

theorem P2_imp_P3 {A : Set X} : P2 (A := A) → P3 (A := A) := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  intro x hxA
  have hx' : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_closure_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have h_inter_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact h_inter_subset hx'