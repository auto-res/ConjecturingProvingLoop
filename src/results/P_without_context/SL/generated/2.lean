

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A :=
by
  intro x hxA
  have hx' : x ∈ interior (closure (interior A)) := h hxA
  exact interior_subset hx'