

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx_closure : x ∈ closure (interior A) :=
    (interior_subset (s := closure (interior A))) hx_int
  exact hx_closure