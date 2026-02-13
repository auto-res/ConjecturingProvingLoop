

theorem Topology.nonempty_interior_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X:=X) A) (hA : (A : Set X).Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP3 hx⟩