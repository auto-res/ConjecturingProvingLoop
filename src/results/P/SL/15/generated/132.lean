

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hAne
  classical
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  have hAeq : A = (∅ : Set X) :=
    Topology.P1_imp_eq_empty_of_empty_interior
      (X := X) (A := A) hP1 hIntEq
  rcases hAne with ⟨x, hx⟩
  have : x ∈ (∅ : Set X) := by
    simpa [hAeq] using hx
  exact this.elim