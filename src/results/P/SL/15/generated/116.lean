

theorem closureInterior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (closure (interior A)).Nonempty := by
  intro hP1 hA
  rcases hA with ⟨x, hx⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  exact ⟨x, hx_cl⟩