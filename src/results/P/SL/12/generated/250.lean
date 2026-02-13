

theorem Topology.interior_eq_compl_closure_compl {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) = (closure ((A : Set X)ᶜ))ᶜ := by
  simpa [compl_compl] using (interior_compl (s := (Aᶜ : Set X)))