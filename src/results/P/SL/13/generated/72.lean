

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure B) := by
  intro x hx
  have h_closure : closure (A : Set X) ⊆ closure B := closure_mono hAB
  exact (interior_mono h_closure) hx