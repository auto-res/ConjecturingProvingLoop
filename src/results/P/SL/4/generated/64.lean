

theorem dense_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure A) := by
  intro hDense
  dsimp [Topology.P1]
  intro x _hx
  -- Since `A` is dense, `closure A = univ`.
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Hence `interior (closure A) = univ`.
  have h_int_eq : interior (closure A) = (Set.univ : Set X) := by
    have h_univ : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure_univ] using h_univ
  -- Therefore `closure (interior (closure A)) = univ`.
  have h_target_eq : closure (interior (closure A)) = (Set.univ : Set X) := by
    have h_closure_univ' : closure (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using closure_univ
    simpa [h_int_eq] using h_closure_univ'
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_target_eq] using this