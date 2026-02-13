

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hAne
  classical
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  have hInnerEmpty : interior (closure (interior A)) = (∅ : Set X) := by
    simpa [hIntEq, closure_empty, interior_empty]
  rcases hAne with ⟨x, hx⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hx
  have : x ∈ (∅ : Set X) := by
    simpa [hInnerEmpty] using hxInt
  exact this.elim