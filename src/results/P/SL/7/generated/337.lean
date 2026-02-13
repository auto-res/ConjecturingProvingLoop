

theorem Topology.nonempty_inter_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A.Nonempty → (A ∩ interior (closure A)).Nonempty := by
  intro hP3 hA
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  exact ⟨x, And.intro hxA hxInt⟩