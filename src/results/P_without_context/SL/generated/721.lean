

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  unfold P2 at hP2
  unfold P3
  intro x hxA
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_closure : closure (interior A) ⊆ closure A := by
    exact closure_mono interior_subset
  have h_int_mono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact h_int_mono hx_in