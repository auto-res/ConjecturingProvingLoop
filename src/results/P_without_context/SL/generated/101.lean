

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P1 A := by
  intro hP2
  unfold P2 P1 at *
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact h_subset hx_int