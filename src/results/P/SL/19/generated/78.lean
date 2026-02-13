

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  have hClose : closure A ⊆ closure B := closure_mono h
  have hInter : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hClose
  exact closure_mono hInter