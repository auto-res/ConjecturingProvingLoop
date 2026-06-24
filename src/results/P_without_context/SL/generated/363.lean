

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  unfold P1 P2 at *
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hxCl : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hxInt
  exact hxCl