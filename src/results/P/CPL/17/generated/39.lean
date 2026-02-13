

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Dense A → Topology.P2 A := by
  intro hA_closed hA_dense
  -- First, deduce that `A` is the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
      hA_dense.closure_eq
    simpa [hA_closed.closure_eq] using h_closure
  -- Conclude using the fact that `P2` holds for `Set.univ`.
  simpa [hA_univ] using (P2_univ (X := X))

theorem P2_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → (Topology.P2 (Aᶜ) ↔ True) := by
  intro hA
  have hP2 : Topology.P2 (Aᶜ) := P2_complement_of_closed (A := A) hA
  constructor
  · intro _; trivial
  · intro _; exact hP2