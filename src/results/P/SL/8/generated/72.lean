

theorem P3_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (closure A)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxA
  have hxCl : (x : X) ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3 hxCl
  simpa [closure_closure] using hxInt