

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  have hcl : (closure (A : Set X)) ⊆ closure (B : Set X) := closure_mono hAB
  exact interior_mono hcl