

theorem exists_infinite_P1 {X : Type*} [TopologicalSpace X] [Infinite X] : ∃ A : Set X, A.Infinite ∧ Topology.P1 A := by
  exact ⟨(Set.univ : Set X), Set.infinite_univ, Topology.P1_univ (X := X)⟩

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (closure A)) : Topology.P3 A := by
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    have h_int_eq : interior (closure A) = closure A := hA.interior_eq
    simpa [h_int_eq] using hx_cl