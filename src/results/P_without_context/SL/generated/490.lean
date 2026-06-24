

theorem P2_implies_P1_and_P3 {A : Set X} :
    P2 A → P1 A ∧ P3 A := by
  intro h
  have hP1 : P1 A := by
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    exact interior_subset hx'
  have hP3 : P3 A := by
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have : x ∈ interior (closure A) := (interior_mono h_subset) hx'
    exact this
  exact And.intro hP1 hP3