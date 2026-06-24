

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P3 A := by
  intro hP2
  dsimp [P2, P3] at hP2 ⊢
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_subset : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure_subset
  exact h_subset hx_int