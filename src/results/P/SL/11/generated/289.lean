

theorem P2_of_P3_and_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A)
    (hEq : interior (closure A) = interior (closure (interior A))) :
    Topology.P2 A := by
  have h : Topology.P3 A ∧
      interior (closure A) = interior (closure (interior A)) := ⟨hP3, hEq⟩
  exact (Topology.P2_iff_P3_and_interior_closure_eq (A := A)).mpr h