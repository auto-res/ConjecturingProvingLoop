

theorem P1_and_P3_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = interior (A : Set X) →
      (Topology.P1 A ∧ Topology.P3 A) := by
  intro hEq
  -- First, note that every point of `A` lies in `interior A`,
  -- since `A ⊆ closure A = interior A`.
  have hA_subset_int : (A : Set X) ⊆ interior (A : Set X) := by
    intro x hx
    have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hx
    simpa [hEq] using hx_cl
  -- Prove `P1`.
  have hP1 : Topology.P1 (A : Set X) := by
    dsimp [Topology.P1]
    intro x hx
    have hx_int : (x : X) ∈ interior (A : Set X) := hA_subset_int hx
    exact subset_closure hx_int
  -- Prove `P3`.
  have hP3 : Topology.P3 (A : Set X) := by
    dsimp [Topology.P3]
    intro x hx
    have hx_int : (x : X) ∈ interior (A : Set X) := hA_subset_int hx
    simpa [hEq, interior_interior] using hx_int
  exact And.intro hP1 hP3