

theorem Topology.closure_iInter_closure_eq_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} (s : ι → Set X) :
    closure (⋂ i, closure (s i) : Set X) = ⋂ i, closure (s i) := by
  have hClosed : IsClosed (⋂ i, closure (s i) : Set X) :=
    isClosed_iInter (fun _ => isClosed_closure)
  simpa using hClosed.closure_eq