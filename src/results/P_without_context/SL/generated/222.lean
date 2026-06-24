

theorem P2_implies_P1_and_P3 {A : Set X} (h : P2 A) : P1 A ∧ P3 A := by
  unfold P1 P2 P3 at *
  refine And.intro ?h1 ?h2
  · intro x hx
    have : x ∈ interior (closure (interior A)) := h hx
    exact interior_subset this
  · intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    have hsub : closure (interior A) ⊆ closure A := closure_mono interior_subset
    have hmono : interior (closure (interior A)) ⊆ interior (closure A) := interior_mono hsub
    exact hmono hx'