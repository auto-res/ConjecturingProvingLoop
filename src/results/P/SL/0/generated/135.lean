

theorem closure_interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X).Nonempty →
      (closure (interior (A : Set X))).Nonempty := by
  intro hP1 hA
  rcases hA with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  exact ⟨x, hx_cl⟩